//! This module provides an iterator type that can wrap a [`Cursor`][Cursor],
//! allowing for iteration over the entries in a database's key-value store.
//!
//! [Cursor]: crate::Cursor

use crate::{Cursor, CursorBasic, CursorReturnedDataHandle};
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

/// Iterator type that wraps a database cursor.
///
/// # Parameters
/// - `'cursor`: Lifetime for the wrapped cursor reference.
/// - `C`: Cursor type to wrap.
/// - `KQ`: Key type that can be used to position the cursor at a specific key.
#[derive(Debug)]
pub struct CursorIter<'cursor, C, KQ: ?Sized> {
    /// The wrapped cursor.
    cursor: &'cursor mut C,

    /// Extra state information for the iterator.
    state: IterState,

    phantom: PhantomData<fn(KQ) -> KQ>,
}

impl<'cursor, C, KQ: ?Sized> CursorIter<'cursor, C, KQ>
where
    C: CursorBasic,
    for<'cursor2> C: Cursor<'cursor2, KQ>,
{
    /// Wraps the specified cursor in an iterator that starts iteration from the
    /// cursor's current position. If the cursor is unpositioned, iteration will
    /// start with the first key in the database; the iteration will be empty if
    /// the database is empty (assuming no error occurs). If the cursor has a
    /// position key, iteration will start with the first key in the database
    /// that is greater than (*not* equal to) that position key; the iteration
    /// will be empty if there is no such key (assuming no error occurs).
    ///
    /// Note: This method makes no guarantee about whether or how the cursor's
    /// position state may be modified by the iterator. Therefore, if you wish
    /// to use a cursor directly after it has been wrapped in an iterator, it is
    /// recommended to first reposition the cursor to a well-defined position.
    pub fn iter(cursor: &'cursor mut C) -> Result<Self, C::Error> {
        Ok(Self {
            cursor,
            state: IterState::MoveToNext,
            phantom: PhantomData::default(),
        })
    }

    /// Similar to [`iter`][iter], except iteration starts at the first key in
    /// the database regardless of the cursor's current position. The iteration
    /// will be empty if the database is empty (assuming no error occurs).
    ///
    /// [iter]: self::CursorIter::iter
    pub fn iter_start(cursor: &'cursor mut C) -> Result<Self, C::Error> {
        Ok(Self {
            cursor,
            state: IterState::MoveToFirst,
            phantom: PhantomData::default(),
        })
    }

    /// Similar to [`iter`][iter], except iteration starts at the specified key
    /// regardless of the cursor's current position. More specifically,
    /// iteration will start with the first key in the database that is greater
    /// than *or* equal to the specified key. The iteration will be empty if
    /// there is no such key (assuming no error occurs).
    ///
    /// [iter]: self::CursorIter::iter
    pub fn iter_from(cursor: &'cursor mut C, key: &KQ) -> Result<Self, C::Error> {
        let cursor_result = cursor.move_to_key_or_after(key).map_err(Into::into)?;
        if cursor_result.is_some() {
            std::mem::drop(cursor_result);
            Ok(Self {
                cursor,
                state: IterState::GetCurrent,
                phantom: PhantomData::default(),
            })
        } else {
            std::mem::drop(cursor_result);
            Ok(Self {
                cursor,
                state: IterState::Finished,
                phantom: PhantomData::default(),
            })
        }
    }
}

impl<'cursor, C, KQ: ?Sized> Iterator for CursorIter<'cursor, C, KQ>
where
    C: CursorBasic,
    for<'cursor2> C: Cursor<'cursor2, KQ>,
{
    type Item = Result<(&'cursor C::ReturnedKey, &'cursor C::ReturnedValue), C::Error>;

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
                    // Here we are essentially casting the result of the cursor
                    // operation to have the longer lifetime 'cursor. This is
                    // safe because of the guarantees made by the
                    // CursorReturnedDataHandle trait. (Since the iterator has a
                    // mutable reference to the cursor and doesn't do any
                    // database mutation, the cursor can't be dropped or used
                    // for mutation as long as the iterator is alive.)
                    let item_refs: (&C::ReturnedKey, &C::ReturnedValue) =
                        (item.0.get(), item.1.get());
                    let item_ptrs: (*const C::ReturnedKey, *const C::ReturnedValue) = (
                        item_refs.0 as *const C::ReturnedKey,
                        item_refs.1 as *const C::ReturnedValue,
                    );
                    let item_cursor_refs: (&'cursor C::ReturnedKey, &'cursor C::ReturnedValue) =
                        unsafe { (&*item_ptrs.0, &*item_ptrs.1) };
                    self.state = IterState::MoveToNext;
                    Some(Ok(item_cursor_refs))
                }
                Ok(None) => {
                    self.state = IterState::Finished;
                    None
                }
                Err(err) => {
                    self.state = IterState::Finished;
                    Some(Err(err))
                }
            }
        }
    }
}

impl<'cursor, C, KQ: ?Sized> FusedIterator for CursorIter<'cursor, C, KQ>
where
    C: CursorBasic,
    for<'cursor2> C: Cursor<'cursor2, KQ>,
{
}
