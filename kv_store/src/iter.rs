//! This module provides an iterator type that implements
//! [`CursorIter`][CursorIter]. It is largely independent of the specific API
//! implementation in use.
//!
//! [CursorIter]: crate::CursorIter

use crate::Cursor;
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
/// - `'cursor`: Lifetime for the wrapped cursor reference.
/// - `C`: Cursor type to wrap.
/// - `E`: Error type that can be produced by the cursor.
/// - `KQ`: Key type that can be used to point the cursor to a specific key in
///   the database.
/// - `KR`: Key object type returned from cursor read operations. May or may not
///   be the same as `KQ`.
/// - `VR`: Value object type returned from cursor read operations.
#[derive(Debug)]
pub struct Iter<'cursor, C, E, KQ, KR, VR> {
    /// The wrapped cursor.
    cursor: &'cursor mut C,

    /// Extra state information for the iterator.
    state: IterState,

    phantom: PhantomData<(E, KQ, KR, VR)>,
}

impl<'cursor, C, E, KQ, KR, VR> Iterator for Iter<'cursor, C, E, KQ, KR, VR>
where
    for<'cursor2> C: Cursor<'cursor2, KQ, Error = E, ReturnedKey = KR, ReturnedValue = VR>,
{
    type Item = Result<(KR, VR), E>;

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

impl<'cursor, C, E, KQ, KR, VR> FusedIterator for Iter<'cursor, C, E, KQ, KR, VR> where
    for<'cursor2> C: Cursor<'cursor2, KQ, Error = E, ReturnedKey = KR, ReturnedValue = VR>
{
}

impl<'cursor, C, E, KQ, KR, VR> crate::CursorIter<'cursor, C, KQ>
    for Iter<'cursor, C, E, KQ, KR, VR>
where
    for<'cursor2> C: Cursor<'cursor2, KQ, Error = E, ReturnedKey = KR, ReturnedValue = VR>,
{
    fn iter(cursor: &'cursor mut C) -> Result<Self, E>
    where
        for<'a> C: Cursor<'a, KQ, Error = E, ReturnedKey = KR, ReturnedValue = VR>,
    {
        Ok(Self {
            cursor,
            state: IterState::MoveToNext,
            phantom: PhantomData::default(),
        })
    }

    fn iter_start(cursor: &'cursor mut C) -> Result<Self, E>
    where
        for<'a> C: Cursor<'a, KQ, Error = E, ReturnedKey = KR, ReturnedValue = VR>,
    {
        Ok(Self {
            cursor,
            state: IterState::MoveToFirst,
            phantom: PhantomData::default(),
        })
    }

    fn iter_from(cursor: &'cursor mut C, key: KQ) -> Result<Self, E>
    where
        for<'a> C: Cursor<'a, KQ, Error = E, ReturnedKey = KR, ReturnedValue = VR>,
    {
        let cursor_result = cursor.move_to_key(key)?;
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
