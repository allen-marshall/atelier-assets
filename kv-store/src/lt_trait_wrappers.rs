//! This module provides wrappers that add unused lifetime parameters to
//! existing traits. It exists solely to work around
//! [this compiler bug/limitation][issue].
//!
//! [issue]: https://github.com/rust-lang/rust/issues/56556

/// Wrapper that adds 2 unused lifetime parameters to [`AsRef`][AsRef].
///
/// [AsRef]: std::convert::AsRef
pub trait AsRefLt2<'lt0, 'lt1, T>: AsRef<T>
where
    T: ?Sized,
{
}

impl<'lt0, 'lt1, T, I> AsRefLt2<'lt0, 'lt1, T> for I
where
    I: ?Sized + AsRef<T>,
    T: ?Sized,
{
}

/// Wrapper that adds 4 unused lifetime parameters to [`AsRef`][AsRef].
///
/// [AsRef]: std::convert::AsRef
pub trait AsRefLt4<'lt0, 'lt1, 'lt2, 'lt3, T>: AsRef<T>
where
    T: ?Sized,
{
}

impl<'lt0, 'lt1, 'lt2, 'lt3, T, I> AsRefLt4<'lt0, 'lt1, 'lt2, 'lt3, T> for I
where
    I: ?Sized + AsRef<T>,
    T: ?Sized,
{
}

/// Wrapper that adds 6 unused lifetime parameters to [`AsRef`][AsRef].
///
/// [AsRef]: std::convert::AsRef
pub trait AsRefLt6<'lt0, 'lt1, 'lt2, 'lt3, 'lt4, 'lt5, T>: AsRef<T>
where
    T: ?Sized,
{
}

impl<'lt0, 'lt1, 'lt2, 'lt3, 'lt4, 'lt5, T, I> AsRefLt6<'lt0, 'lt1, 'lt2, 'lt3, 'lt4, 'lt5, T> for I
where
    I: ?Sized + AsRef<T>,
    T: ?Sized,
{
}
