use core::{marker::PhantomData, mem::ManuallyDrop};

use crate::{Asynchronous, IsAsync, Synchronous};

/// Stores `IfSync` if `A` is [`Synchronous`], and `IfAsync` if `A` is [`Asynchronous`].
///
/// # Note
///
/// Due to limitations in Rust's type system, this type stores a union of `IfSync` and `IfAsync`,
/// rather than only `IfSync` or `IfAsync`.
///
/// This may change in the future (and/or in nightly), as const generics and/or specialization will
/// allow us to store only the relevant variant.
pub union OneOf<A: IsAsync, IfSync, IfAsync> {
    /// Active field if `A::IS_ASYNC` is `false`.
    if_sync: ManuallyDrop<IfSync>,
    /// Active field if `A::IS_ASYNC` is `true`.
    if_async: ManuallyDrop<IfAsync>,
    /// Marker to ensure that the parameter `A` is used. Never active.
    _marker: PhantomData<A>,
}

impl<A: IsAsync, IfSync, IfAsync> Drop for OneOf<A, IfSync, IfAsync> {
    fn drop(&mut self) {
        if A::IS_ASYNC {
            // SAFETY: checked `A::IS_ASYNC` above.
            unsafe { ManuallyDrop::drop(&mut self.if_async) }
        } else {
            // SAFETY: checked `!A::IS_ASYNC` above.
            unsafe { ManuallyDrop::drop(&mut self.if_sync) }
        }
    }
}

impl<IfSync, IfAsync> OneOf<Synchronous, IfSync, IfAsync> {
    /// Returns a [`OneOf`] which stores its [`Synchronous`] variant.
    ///
    /// ```
    /// # use async_if::OneOf;
    /// assert_eq!(OneOf::<_, _, ()>::new_sync(5).into_sync(), Ok(5));
    /// assert_eq!(OneOf::<_, _, ()>::new_sync(5).into_async(), Err(5));
    /// ```
    pub const fn new_sync(value: IfSync) -> Self {
        OneOf {
            if_sync: ManuallyDrop::new(value),
        }
    }
}

impl<IfSync, IfAsync> OneOf<Asynchronous, IfSync, IfAsync> {
    /// Returns a [`OneOf`] which stores its [`Asynchronous`] variant.
    ///
    /// ```
    /// # use async_if::OneOf;
    /// assert_eq!(OneOf::<_, (), _>::new_async(5).into_async(), Ok(5));
    /// assert_eq!(OneOf::<_, (), _>::new_async(5).into_sync(), Err(5));
    /// ```
    pub const fn new_async(value: IfAsync) -> Self {
        OneOf {
            if_async: ManuallyDrop::new(value),
        }
    }
}

/// Instantiation methods.
impl<A: IsAsync, IfSync, IfAsync> OneOf<A, IfSync, IfAsync> {
    /// Returns a [`OneOf`] which computes its variant based on whether `A` by either calling
    /// `if_sync` or `if_async`.
    pub fn new(if_sync: impl FnOnce() -> IfSync, if_async: impl FnOnce() -> IfAsync) -> Self {
        if A::IS_ASYNC {
            Self {
                if_async: ManuallyDrop::new(if_async()),
            }
        } else {
            Self {
                if_sync: ManuallyDrop::new(if_sync()),
            }
        }
    }

    /// Returns a [`OneOf`] which computes its variant based on whether `A` by either calling
    /// `if_sync` or `if_async`, returning any encountered [`Err`].
    pub fn try_new<E>(
        if_sync: impl FnOnce() -> Result<IfSync, E>,
        if_async: impl FnOnce() -> Result<IfAsync, E>,
    ) -> Result<Self, E> {
        if A::IS_ASYNC {
            Ok(Self {
                if_async: ManuallyDrop::new(if_async()?),
            })
        } else {
            Ok(Self {
                if_sync: ManuallyDrop::new(if_sync()?),
            })
        }
    }
}

/// Safe access methods.
impl<A: IsAsync, IfSync, IfAsync> OneOf<A, IfSync, IfAsync> {
    /// Returns the stored variant wrapped in an [`Ok`] if it is [`Asynchronous`], or in an [`Err`]
    /// if it is [`Synchronous`].
    pub fn into_async(self) -> Result<IfAsync, IfSync> {
        if A::IS_ASYNC {
            // SAFETY: checked `A::IS_ASYNC` above.
            Ok(unsafe { self.into_async_unchecked() })
        } else {
            // SAFETY: checked `A::IS_ASYNC` above.
            Err(unsafe { self.into_sync_unchecked() })
        }
    }

    /// Returns the stored variant wrapped in an [`Ok`] if it is [`Synchronous`], or in an [`Err`]
    /// if it is [`Asynchronous`].
    pub fn into_sync(self) -> Result<IfSync, IfAsync> {
        match self.into_async() {
            Ok(value) => Err(value),
            Err(value) => Ok(value),
        }
    }

    /// Returns an [`Ok`] reference to the stored variant if it is [`Asynchronous`] and an [`Err`]
    /// reference to the stored variant if it is [`Synchronous`].
    pub fn as_async(&self) -> Result<&IfAsync, &IfSync> {
        self.as_ref().into_async()
    }

    /// Returns an [`Ok`] reference to the stored variant if it is [`Synchronous`] and an [`Err`]
    /// reference to the stored variant if it is [`Asynchronous`].
    pub fn as_sync(&self) -> Result<&IfSync, &IfAsync> {
        self.as_ref().into_sync()
    }

    /// Returns an [`Ok`] mut reference to the stored variant if it is [`Asynchronous`] and an
    /// [`Err`] mut reference to the stored variant if it is [`Synchronous`].
    pub fn as_async_mut(&mut self) -> Result<&mut IfAsync, &mut IfSync> {
        self.as_mut().into_async()
    }

    /// Returns an [`Ok`] mut reference to the stored variant if it is [`Synchronous`] and an
    /// [`Err`] mut reference to the stored variant if it is [`Asynchronous`].
    pub fn as_sync_mut(&mut self) -> Result<&mut IfSync, &mut IfAsync> {
        self.as_mut().into_sync()
    }

    /// Returns a [`OneOf`] which stores a reference to its inner value.
    pub fn as_ref(&self) -> OneOf<A, &IfSync, &IfAsync> {
        if A::IS_ASYNC {
            // SAFETY: checked `A::IS_ASYNC` above.
            let value = unsafe { self.as_async_unchecked() };

            OneOf {
                if_async: ManuallyDrop::new(value),
            }
        } else {
            // SAFETY: checked `!A::IS_ASYNC` above.
            let value = unsafe { self.as_sync_unchecked() };

            OneOf {
                if_sync: ManuallyDrop::new(value),
            }
        }
    }

    /// Returns a [`OneOf`] which stores a mutable reference to its inner value.
    pub fn as_mut(&mut self) -> OneOf<A, &mut IfSync, &mut IfAsync> {
        if A::IS_ASYNC {
            // SAFETY: checked `IS_ASYNC` above.
            let value = unsafe { self.as_async_mut_unchecked() };

            OneOf {
                if_async: ManuallyDrop::new(value),
            }
        } else {
            // SAFETY: checked `!A::IS_ASYNC` above.
            let value = unsafe { self.as_sync_mut_unchecked() };

            OneOf {
                if_sync: ManuallyDrop::new(value),
            }
        }
    }
}

/// Helpers.
impl<A: IsAsync, IfSync, IfAsync> OneOf<A, IfSync, IfAsync> {
    /// Returns a [`OneOf`] which stores the result of calling `if_async` or `if_sync` on its inner
    /// value.
    pub fn map<IfAsyncR, IfSyncR>(
        self,
        if_async: impl FnOnce(IfAsync) -> IfAsyncR,
        if_sync: impl FnOnce(IfSync) -> IfSyncR,
    ) -> OneOf<A, IfSyncR, IfAsyncR> {
        if A::IS_ASYNC {
            // SAFETY: checked `A::IS_ASYNC` above.
            let value = unsafe { self.into_async_unchecked() };

            OneOf {
                if_async: ManuallyDrop::new(if_async(value)),
            }
        } else {
            // SAFETY: checked `!A::IS_ASYNC` above.
            let value = unsafe { self.into_sync_unchecked() };

            OneOf {
                if_sync: ManuallyDrop::new(if_sync(value)),
            }
        }
    }

    /// Returns a [`OneOf`] which the inner value of both `self` and `other`.
    pub fn zip<OtherIfSync, OtherIfAsync>(
        self,
        other: OneOf<A, OtherIfSync, OtherIfAsync>,
    ) -> OneOf<A, (IfSync, OtherIfSync), (IfAsync, OtherIfAsync)> {
        if A::IS_ASYNC {
            // SAFETY: checked `A::IS_ASYNC` above.
            let value = unsafe { self.into_async_unchecked() };
            // SAFETY: checked `A::IS_ASYNC` above, and `other` uses the same `A` argument.
            let other = unsafe { other.into_async_unchecked() };

            OneOf {
                if_async: ManuallyDrop::new((value, other)),
            }
        } else {
            // SAFETY: checked `!A::IS_ASYNC` above.
            let value = unsafe { self.into_sync_unchecked() };
            // SAFETY: checked `!A::IS_ASYNC` above, and `other` uses the same `A` argument.
            let other = unsafe { other.into_sync_unchecked() };

            OneOf {
                if_sync: ManuallyDrop::new((value, other)),
            }
        }
    }
}

/// Unsafe access methods.
impl<A: IsAsync, IfSync, IfAsync> OneOf<A, IfSync, IfAsync> {
    /// Returns the inner `IfAsync` variant without the compile-time guarantee that `A` is
    /// [`Asynchronous`].
    ///
    /// # Safety
    ///
    /// The caller must ensure that `A::IS_ASYNC` is `true`.
    pub unsafe fn into_async_unchecked(self) -> IfAsync {
        debug_assert!(A::IS_ASYNC);

        // SAFETY: `A::IS_ASYNC` is guaranteed to be `true` by the caller, so `self.is_async` is
        // set.
        let value = core::ptr::read(&self.if_async);

        core::mem::forget(self);

        ManuallyDrop::into_inner(value)
    }

    /// Returns the inner `IfSync` variant without the compile-time guarantee that `A` is
    /// [`Synchronous`].
    ///
    /// # Safety
    ///
    /// The caller must ensure that `A::IS_ASYNC` is `false`.
    pub unsafe fn into_sync_unchecked(self) -> IfSync {
        debug_assert!(!A::IS_ASYNC);

        // SAFETY: `A::IS_ASYNC` is guaranteed to be `false` by the caller, so `self.is_sync` is
        // set.
        let value = core::ptr::read(&self.if_sync);

        core::mem::forget(self);

        ManuallyDrop::into_inner(value)
    }

    /// Returns a reference to the inner `IfAsync` variant without the compile-time guarantee that
    /// `A` is [`Asynchronous`].
    ///
    /// # Safety
    ///
    /// The caller must ensure that `A::IS_ASYNC` is `true`.
    pub unsafe fn as_async_unchecked(&self) -> &IfAsync {
        debug_assert!(A::IS_ASYNC);

        // SAFETY: `A::IS_ASYNC` is guaranteed to be `true` by the caller, so `self.is_async` is
        // set.
        &self.if_async
    }

    /// Returns a reference to the inner `IfSync` variant without the compile-time guarantee that
    /// `A` is [`Synchronous`].
    ///
    /// # Safety
    ///
    /// The caller must ensure that `A::IS_ASYNC` is `false`.
    pub unsafe fn as_sync_unchecked(&self) -> &IfSync {
        debug_assert!(!A::IS_ASYNC);

        // SAFETY: `A::IS_ASYNC` is guaranteed to be `false` by the caller, so `self.is_sync` is
        // set.
        &self.if_sync
    }

    /// Returns a mut reference to the inner `IfAsync` variant without the compile-time guarantee
    /// that `A` is [`Asynchronous`].
    ///
    /// # Safety
    ///
    /// The caller must ensure that `A::IS_ASYNC` is `true`.
    pub unsafe fn as_async_mut_unchecked(&mut self) -> &mut IfAsync {
        debug_assert!(A::IS_ASYNC);

        // SAFETY: `A::IS_ASYNC` is guaranteed to be `true` by the caller, so `self.is_async` is
        // set.
        &mut self.if_async
    }

    /// Returns a mut reference to the inner `IfSync` variant without the compile-time guarantee
    /// that `A` is [`Synchronous`].
    ///
    /// # Safety
    ///
    /// The caller must ensure that `A::IS_ASYNC` is `false`.
    pub unsafe fn as_sync_mut_unchecked(&mut self) -> &mut IfSync {
        debug_assert!(!A::IS_ASYNC);

        // SAFETY: `A::IS_ASYNC` is guaranteed to be `false` by the caller, so `self.is_sync` is
        // set.
        &mut self.if_sync
    }
}

impl<A: IsAsync, IfSync: Default, IfAsync: Default> Default for OneOf<A, IfSync, IfAsync> {
    fn default() -> Self {
        Self::new(Default::default, Default::default)
    }
}

impl<A: IsAsync, IfSync: Clone, IfAsync: Clone> Clone for OneOf<A, IfSync, IfAsync> {
    fn clone(&self) -> Self {
        self.as_ref().map(Clone::clone, Clone::clone)
    }
}

impl<A: IsAsync, IfSync: core::fmt::Debug, IfAsync: core::fmt::Debug> core::fmt::Debug
    for OneOf<A, IfSync, IfAsync>
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self.as_async() {
            Ok(value) => value.fmt(f),
            Err(value) => value.fmt(f),
        }
    }
}

impl<A: IsAsync, IfSync: core::cmp::PartialEq, IfAsync: core::cmp::PartialEq> core::cmp::PartialEq
    for OneOf<A, IfSync, IfAsync>
{
    fn eq(&self, other: &Self) -> bool {
        match self.as_ref().zip(other.as_ref()).into_async() {
            Ok((left, right)) => left == right,
            Err((left, right)) => left == right,
        }
    }
}

impl<A: IsAsync, IfSync: core::cmp::Eq, IfAsync: core::cmp::Eq> core::cmp::Eq
    for OneOf<A, IfSync, IfAsync>
{
}

impl<A: IsAsync, IfSync: core::cmp::PartialOrd, IfAsync: core::cmp::PartialOrd>
    core::cmp::PartialOrd for OneOf<A, IfSync, IfAsync>
{
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        match self.as_ref().zip(other.as_ref()).into_async() {
            Ok((left, right)) => left.partial_cmp(right),
            Err((left, right)) => left.partial_cmp(right),
        }
    }
}

impl<A: IsAsync, IfSync: core::cmp::Ord, IfAsync: core::cmp::Ord> core::cmp::Ord
    for OneOf<A, IfSync, IfAsync>
{
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        match self.as_ref().zip(other.as_ref()).into_async() {
            Ok((left, right)) => left.cmp(right),
            Err((left, right)) => left.cmp(right),
        }
    }
}

impl<A: IsAsync, IfSync: core::hash::Hash, IfAsync: core::hash::Hash> core::hash::Hash
    for OneOf<A, IfSync, IfAsync>
{
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        match self.as_async() {
            Ok(value) => value.hash(state),
            Err(value) => value.hash(state),
        }
    }
}

impl<A: IsAsync, IfSync: core::ops::Deref, IfAsync: core::ops::Deref<Target = IfSync::Target>>
    core::ops::Deref for OneOf<A, IfSync, IfAsync>
{
    type Target = IfSync::Target;

    fn deref(&self) -> &Self::Target {
        match self.as_async() {
            Ok(value) => value.deref(),
            Err(value) => value.deref(),
        }
    }
}

impl<
        A: IsAsync,
        IfSync: core::ops::DerefMut,
        IfAsync: core::ops::DerefMut<Target = IfSync::Target>,
    > core::ops::DerefMut for OneOf<A, IfSync, IfAsync>
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self.as_async_mut() {
            Ok(value) => value.deref_mut(),
            Err(value) => value.deref_mut(),
        }
    }
}
