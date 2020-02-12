//! This module provides an iterator type that implements
//! [`CursorIterator`][CursorIterator] for cursors that meet certain
//! requirements.
//!
//! [CursorIterator]: crate::CursorIterator

use crate::{Cursor, CursorIterator};
use std::iter::FusedIterator;
use std::marker::PhantomData;

/// State held by the iterator in addition to the cursor's internal state.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum IterState {
    /// In this state, the iterator's next operation should be to move the
    /// cursor to the first key in the database.
    MoveToFirst,

    /// In this state, the iterator's next operation should be to move the
    /// cursor to the next key in the database.
    MoveToNext,

    /// In this state, the iterator's next operation should be to read the entry
    /// from the cursor's current position.
    GetCurrent,

    /// In this state, the iterator has terminated and should not produce any
    /// more items. This can be due to normal termination or an error.
    Finished,
}

/// Iterator type that simply wraps a database cursor.
///
/// # Parameters
/// - `'txn`: Lifetime of the transaction reference used to construct the
///   cursor.
/// - `'cursor`: Lifetime for the wrapped cursor reference.
/// - `C`: Cursor type to wrap.
/// - `KQ`: Key type that can be used to position the cursor at a specific key.
#[derive(Debug)]
pub struct CursorIter<'txn, 'cursor, C, KQ> {
    /// The wrapped cursor.
    cursor: &'cursor mut C,

    /// Extra state information for the iterator.
    state: IterState,

    phantom: PhantomData<(&'txn (), KQ)>,
}

impl<'txn, 'cursor, C, KQ> Iterator for CursorIter<'txn, 'cursor, C, KQ>
where
    C: 'txn + Cursor<'txn, KQ>,
{
    type Item = Result<(C::ReturnedKey, C::ReturnedValue), C::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.state == IterState::Finished {
            None
        } else {
            let cursor_result = match self.state {
                IterState::MoveToFirst => self.cursor.move_to_first(),
                IterState::MoveToNext => self.cursor.move_to_next(),
                IterState::GetCurrent => self.cursor.get(),

                // IterState::Finished should be impossible in this branch.
                IterState::Finished => panic!(),
            };
            match cursor_result {
                Ok(Some(item)) => {
                    self.state = IterState::MoveToNext;
                    Some(Ok(item.into()))
                }
                Ok(None) => {
                    self.state = IterState::Finished;
                    None
                }
                Err(err) => {
                    self.state = IterState::Finished;
                    Some(Err(err.into()))
                }
            }
        }
    }
}

impl<'txn, 'cursor, C, KQ> FusedIterator for CursorIter<'txn, 'cursor, C, KQ> where
    C: 'txn + Cursor<'txn, KQ>
{
}

impl<'txn, 'cursor, C, KQ> CursorIterator<'txn, 'cursor, C, KQ> for CursorIter<'txn, 'cursor, C, KQ>
where
    C: 'txn + Cursor<'txn, KQ>,
{
    fn iter(cursor: &'cursor mut C) -> Result<Self, C::Error>
    where
        Self: 'cursor,
        C: 'cursor,
    {
        Ok(Self {
            cursor,
            state: IterState::MoveToNext,
            phantom: PhantomData::default(),
        })
    }

    fn iter_start(cursor: &'cursor mut C) -> Result<Self, C::Error>
    where
        Self: 'cursor,
        C: 'cursor,
    {
        Ok(Self {
            cursor,
            state: IterState::MoveToFirst,
            phantom: PhantomData::default(),
        })
    }

    fn iter_from(cursor: &'cursor mut C, key: KQ) -> Result<Self, C::Error>
    where
        Self: 'cursor,
        C: 'cursor,
    {
        let cursor_result = cursor.move_to_key_or_after(key)?;
        if cursor_result.is_some() {
            Ok(Self {
                cursor,
                state: IterState::GetCurrent,
                phantom: PhantomData::default(),
            })
        } else {
            Ok(Self {
                cursor,
                state: IterState::Finished,
                phantom: PhantomData::default(),
            })
        }
    }
}
