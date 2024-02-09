use core::{
    fmt::Debug,
    future::{ready, Future, Ready},
    marker::PhantomData,
    pin::Pin,
    task::{Context, Poll},
};

use crate::{helpers::poll_expecting_ready, AsyncIf, Asynchronous, IsAsync, OneOf, Synchronous};

/// Returns a [`Future`] which implements [`AsyncIf<Asynchronous>`].
pub fn from_future<F: Future>(future: F) -> impl AsyncIf<Asynchronous, Output = F::Output> {
    PossiblySyncFuture::new_async(future)
}

/// Returns a [`Future`] which implements [`AsyncIf<Synchronous>`].
pub fn from_value<T>(value: T) -> impl AsyncIf<Synchronous, Output = T> {
    ready(value)
}

/// A wrapper around a regular [`Future`] which guarantees that it will execute synchronously if
/// `A` is [`Synchronous`].
#[repr(transparent)]
#[derive(Clone, Debug)]
pub struct PossiblySyncFuture<A: IsAsync, F: Future> {
    future: F,
    _marker: PhantomData<A>,
}

impl<A: IsAsync, F: Future> Future for PossiblySyncFuture<A, F> {
    type Output = F::Output;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<F::Output> {
        // SAFETY: `self.future` is a structural field which we never access outside of this
        // function, and therefore we cannot break its pin projection guarantees.
        let future = unsafe { self.map_unchecked_mut(|x| &mut x.future) };

        future.poll(cx)
    }
}

// SAFETY: creating a `PossiblySyncFuture` is an unsafe operation; callers of `new_unchecked()` and
// `infer_unchecked()` must ensure that the future is actually synchronous if they pass
// `A == Synchronous`.
unsafe impl<A: IsAsync, F: Future> AsyncIf<A> for PossiblySyncFuture<A, F> {
    unsafe fn get_unchecked(self) -> Self::Output
    where
        Self: Sized,
    {
        poll_expecting_ready(self)
            .expect("future given to returned PossiblySyncFuture returned Poll::Pending")
    }
}

impl<T> PossiblySyncFuture<Synchronous, Ready<T>> {
    /// Returns a new [`PossiblySyncFuture`] which wraps the given value, guaranteeing that it can
    /// be run synchronously.
    pub fn new_sync(value: T) -> PossiblySyncFuture<Synchronous, Ready<T>> {
        PossiblySyncFuture {
            future: ready(value),
            _marker: PhantomData,
        }
    }
}

impl<F: Future> PossiblySyncFuture<Asynchronous, F> {
    /// Returns a new [`PossiblySyncFuture`] which wraps the given [`Future`], making no guarantees
    /// on whether or not it can be run synchronously.
    pub const fn new_async(future: F) -> PossiblySyncFuture<Asynchronous, F> {
        PossiblySyncFuture {
            future,
            _marker: PhantomData,
        }
    }
}

impl<A: IsAsync, F: Future> PossiblySyncFuture<A, F> {
    /// Creates a new [`PossiblySyncFuture`] from the given future with no guarantee that the future
    /// will _actually_ execute synchronously.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the given `future` will immediately return [`Poll::Ready`] when
    /// polled if `A` is [`Synchronous`](crate::Synchronous).
    pub const unsafe fn new_unchecked(future: F) -> Self {
        Self {
            future,
            _marker: PhantomData,
        }
    }

    /// Creates a new [`PossiblySyncFuture`] from the given future with no guarantee that the future
    /// will _actually_ execute synchronously. A [`PhantomData<IsAsync>`] can be given as second
    /// argument to infer the [`IsAsync`] type parameter without specifying it explicitly.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the given `future` will immediately return [`Poll::Ready`] when
    /// polled if `A` is [`Synchronous`](crate::Synchronous).
    pub const unsafe fn infer_unchecked(future: F, _: PhantomData<A>) -> Self {
        Self {
            future,
            _marker: PhantomData,
        }
    }

    /// Returns the underlying [`Future`].
    pub fn into_inner(self) -> F {
        self.future
    }
}

impl<T> From<T> for PossiblySyncFuture<Synchronous, Ready<T>> {
    fn from(value: T) -> Self {
        Self::new_sync(value)
    }
}

impl<F: Future> From<F> for PossiblySyncFuture<Asynchronous, F> {
    fn from(future: F) -> Self {
        Self::new_async(future)
    }
}

/// A [`Future`] which behaves like [`Ready`] if `A` is [`Synchronous`], and like `F` otherwise.
pub struct FutureIf<A: IsAsync, F: Future>(OneOf<A, Option<F::Output>, F>);

impl<F: Future> FutureIf<Synchronous, F> {
    /// Returns a new [`FutureIf`] future which wraps the given `value`, guaranteeing that it can
    /// be run synchronously.
    pub const fn new_sync(value: F::Output) -> Self {
        Self(OneOf::<Synchronous, _, _>::new_sync(Some(value)))
    }
}

impl<F: Future> FutureIf<Asynchronous, F> {
    /// Returns a new [`FutureIf`] future which wraps the given [`Future`], making no guarantees
    /// on whether or not it can be run synchronously.
    pub const fn new_async(future: F) -> Self {
        Self(OneOf::<Asynchronous, _, _>::new_async(future))
    }
}

impl<A: IsAsync, F: Future> Future for FutureIf<A, F>
where
    F::Output: Unpin,
{
    type Output = F::Output;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<F::Output> {
        // SAFETY: pinning is not structural for `FutureIf`.
        // See https://doc.rust-lang.org/std/pin/index.html.
        let data = unsafe { &mut self.get_unchecked_mut().0 };

        if A::IS_ASYNC {
            // SAFETY: checked `A::IS_ASYNC` above.
            let future = unsafe { data.as_async_mut_unchecked() };
            let future = unsafe { Pin::new_unchecked(future) };

            future.poll(cx)
        } else {
            // SAFETY: checked `!A::IS_ASYNC` above.
            let option = unsafe { data.as_sync_mut_unchecked() };

            Poll::Ready(option.take().expect("poll() called more than once"))
        }
    }
}

// SAFETY: `choose()`, which creates `FutureIf<A>`, uses `A` to determine which union field is
// active and given a value at initialization. Therefore when `A` is `Synchronous` the `if_sync`
// field is used when polling, which guarantees a synchronous completion.
unsafe impl<A: IsAsync, F: Future> AsyncIf<A> for FutureIf<A, F>
where
    F::Output: Unpin,
{
    unsafe fn get_unchecked(mut self) -> Self::Output
    where
        Self: Sized,
    {
        self.0
            .as_sync_mut_unchecked() // Same SAFETY guarantee as needed to call `get_unchecked()`.
            .take()
            .expect("get() called after poll()")
    }
}

impl<A: IsAsync, F: Future> Debug for FutureIf<A, F>
where
    F: Debug,
    F::Output: Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self.0.as_async() {
            Ok(value) => f.debug_struct("FutureIf").field("if_async", value).finish(),
            Err(value) => f.debug_struct("FutureIf").field("if_sync", value).finish(),
        }
    }
}

impl<A: IsAsync, F: Future> Clone for FutureIf<A, F>
where
    F: Clone,
    F::Output: Clone,
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

/// Returns a [`Future`] which is implemented using `if_sync` if `A` is [`Synchronous`], and with
/// `if_async` if `A` is [`Asynchronous`].
pub fn choose<A: IsAsync, F: Future>(
    if_sync: impl FnOnce() -> F::Output,
    if_async: impl FnOnce() -> F,
) -> FutureIf<A, F> {
    FutureIf(OneOf::new(move || Some(if_sync()), if_async))
}

/// Trait which describes how to allocate an asynchronous [`Future`] in [`alloc_future_if()`].
pub trait AllocFuture {
    type Output<'f, F: Future + 'f>: Future<Output = F::Output> + 'f
    where
        Self: 'f;

    fn alloc<'f, 'bump: 'f, F: Future + 'f>(&'bump self, value: F) -> Self::Output<'f, F>
    where
        <F as Future>::Output: Unpin + 'f;
}

/// Returns `future` if it is [`Synchronous`], and a type-erased `future` allocated by `alloc`
/// otherwise.
///
/// This function is used to allow recursive calls between async functions which typically require
/// returned futures to be allocated on the heap to avoid infinite stack growth. For synchronous
/// futures, however, storing their state on the stack is fine and allocating them on the heap would
/// be wasteful.
///
/// If you want to allocate futures on the heap using a [`Box`](alloc::boxed::Box), use
/// [`box_future_if()`] instead.
///
/// When using the [`#[async_if]`](crate::async_if) attribute, use the `alloc_with` argument to
/// specify the `alloc` value.
///
/// # Example
///
/// ```
/// # #[cfg(feature = "bumpalo")]
/// # {
/// # use async_if::{Asynchronous, AsyncIf, IsAsync, Synchronous, async_if};
/// #[async_if(A, alloc_with = bump)]
/// async fn factorial<A: IsAsync>(bump: &bumpalo::Bump, n: u8) -> u64 {
///     if n == 0 { 1 } else { n as u64 * factorial::<A>(bump, n - 1).await }
/// }
///
/// let bump = bumpalo::Bump::new();  // Bumpalo support requires the `bumpalo` feature.
/// assert_eq!(factorial::<Synchronous>(&bump, 5).get(), 120);
/// assert_eq!(bump.allocated_bytes(), 0);
///
/// # tokio::runtime::Builder::new_current_thread().build().unwrap().block_on(async {
/// assert_eq!(factorial::<Asynchronous>(&bump, 5).await, 120);
/// assert_ne!(bump.allocated_bytes(), 0);
/// # });
/// # }
/// ```
///
/// # Example
///
/// Manually using [`alloc_future_if()`]:
///
/// ```
/// # #[cfg(feature = "bumpalo")]
/// # {
/// # use async_if::{Asynchronous, AsyncIf, IsAsync, Synchronous, async_move, alloc_future_if};
/// fn factorial<A: IsAsync>(bump: &bumpalo::Bump, n: u8) -> impl AsyncIf<A, Output = u64> + '_ {
///     async_move! {
///         if n == 0 {
///             1
///         } else {
///             n as u64 * alloc_future_if(bump, factorial::<A>(bump, n - 1)).await
///         }
///     }
/// }
///
/// let bump = bumpalo::Bump::new();  // Bumpalo support requires the `bumpalo` feature.
/// assert_eq!(factorial::<Synchronous>(&bump, 5).get(), 120);
/// assert_eq!(bump.allocated_bytes(), 0);
///
/// # tokio::runtime::Builder::new_current_thread().build().unwrap().block_on(async {
/// assert_eq!(factorial::<Asynchronous>(&bump, 5).await, 120);
/// assert_ne!(bump.allocated_bytes(), 0);
/// # });
/// # }
/// ```
pub fn alloc_future_if<'f, 'alloc: 'f, A: IsAsync, Alloc: AllocFuture, F: AsyncIf<A> + 'f>(
    alloc: &'alloc Alloc,
    future: F,
) -> FutureIf<A, <Alloc as AllocFuture>::Output<'f, F>>
where
    <F as Future>::Output: Unpin + 'f,
{
    future.and_then(move |result| result, move |if_async| alloc.alloc(if_async))
}

/// Returns `future` if it is [`Synchronous`], and `future` boxed on the heap otherwise.
///
/// If you want to control how futures are allocated, use [`alloc_future_if()`] instead.
///
/// When using the [`#[async_if]`](crate::async_if) attribute, use the `alloc_with_box` argument.
///
/// # Example
///
/// ```
/// # use async_if::{Asynchronous, AsyncIf, IsAsync, Synchronous, async_if};
/// #[async_if(A, alloc_with_box)]
/// async fn factorial<A: IsAsync>(n: u8) -> u64 {
///     if n == 0 { 1 } else { n as u64 * factorial::<A>(n - 1).await }
/// }
///
/// assert_eq!(factorial::<Synchronous>(5).get(), 120);
/// # tokio::runtime::Builder::new_current_thread().build().unwrap().block_on(async {
/// assert_eq!(factorial::<Asynchronous>(5).await, 120);
/// # });
/// ```
///
/// # Example
///
/// Manually using [`box_future_if()`]:
///
/// ```
/// # use async_if::{Asynchronous, AsyncIf, IsAsync, Synchronous, async_move, box_future_if};
/// fn factorial<A: IsAsync>(n: u8) -> impl AsyncIf<A, Output = u64> {
///     async_move! {
///         if n == 0 { 1 } else { n as u64 * box_future_if(factorial::<A>(n - 1)).await }
///     }
/// }
///
/// assert_eq!(factorial::<Synchronous>(5).get(), 120);
/// # tokio::runtime::Builder::new_current_thread().build().unwrap().block_on(async {
/// assert_eq!(factorial::<Asynchronous>(5).await, 120);
/// # });
/// ```
#[cfg(feature = "alloc")]
pub fn box_future_if<'f, A: IsAsync, F: AsyncIf<A> + 'f>(
    future: F,
) -> FutureIf<A, Pin<alloc::boxed::Box<dyn Future<Output = F::Output> + 'f>>>
where
    F::Output: Unpin,
{
    alloc_future_if(&AllocFutureWithBox, future)
}

/// An [`AllocFuture`] implementation which allocates futures on the heap in a
/// [`Box`](alloc::boxed::Box).
#[cfg(feature = "alloc")]
#[doc(hidden)]
pub struct AllocFutureWithBox;

#[cfg(feature = "alloc")]
impl AllocFuture for AllocFutureWithBox {
    type Output<'f, F: Future + 'f> = Pin<alloc::boxed::Box<dyn Future<Output = F::Output> + 'f>>;

    fn alloc<'f, 'bump: 'f, F: Future + 'f>(&'bump self, value: F) -> Self::Output<'f, F>
    where
        <F as Future>::Output: 'f,
    {
        alloc::boxed::Box::pin(value)
    }
}

#[cfg(feature = "bumpalo")]
impl AllocFuture for bumpalo::Bump {
    type Output<'f, F: Future + 'f> =
        Pin<bumpalo::boxed::Box<'f, dyn Future<Output = F::Output> + 'f>>;

    fn alloc<'f, 'bump: 'f, F: Future + 'f>(&'bump self, value: F) -> Self::Output<'f, F>
    where
        <F as Future>::Output: 'f,
    {
        let boxed = bumpalo::boxed::Box::new_in(value, self);
        let type_erased = unsafe {
            bumpalo::boxed::Box::from_raw(
                bumpalo::boxed::Box::into_raw(boxed) as *mut (dyn Future<Output = F::Output> + 'f)
            )
        };

        type_erased.into()
    }
}
