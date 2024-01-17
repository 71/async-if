//! # async-if
//!
//! An experimental library for generic async functions.
//!
//! ## Overview
//!
//! [`AsyncIf`] is a [`Future`] additionally parameterized with an [`IsAsync`] parameter which may
//! be one of two types:
//!
//! - [`Asynchronous`] for functions which _may_ execute asynchronously.
//! - [`Synchronous`] for functions which _always_ execute synchronously.
//!
//! [`AsyncIf<Synchronously>`] is known to be synchronous at compile-time, allowing safe access
//! outside of async functions (using [`AsyncIf::get()`]) and recursion without allocations (using
//! [`alloc_future_if()`]).
//!
//! ## Macros
//!
//! - Use [`#[async_if(A)]`](async_if) and [`#[async_when(V)`](async_when) to convert async
//!   functions into [`AsyncIf`]-returning functions which preserve the [`IsAsync`] nature of the
//!   futures they await.
//!
//! - Use [`async_move!`] (respectively [`async_ref!`]) to convert `async move` (respectively
//!   `async`) blocks into [`AsyncIf`] futures which preserve the [`IsAsync`] nature of the futures
//!   they await.
//!
//! # Utilities
//!
//! Additional utilities are provided to build [`AsyncIf`] futures:
//!
//! - [`choose()`] constructs an [`AsyncIf`] future from two closures, one which specifies the
//!   [`Synchronous`] behavior and one which specifies the [`Asynchronous`] behavior.
//!
//! - [`alloc_future_if()`] and [`box_future_if()`] allow the execution of recursive async functions
//!   by automatically allocating futures **only when they are not known to be [`Synchronous`]**.
#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;

use core::{future::Future, marker::PhantomData};

pub(crate) mod futures;
pub(crate) mod helpers;

/// Transforms an `async` function into a function which supports both synchronous and asynchronous
/// execution depending on the value of a type parameter `A`.
///
/// The resulting function will return `impl AsyncIf<A, Output = T>` where `T` is the return type of
/// the function.
///
/// See [`AsyncIf`] for more information.
///
/// # Example
///
/// ```
/// # use async_if::{async_if, choose, Asynchronous, Synchronous, IsAsync, AsyncIf as _};
/// # use std::time::{Duration, Instant};
/// #[async_if(A)]
/// async fn sleep<A: IsAsync>(duration: Duration) {
///     choose::<A, _>(
///         move || std::thread::sleep(duration),
///         move || Box::pin(tokio::time::sleep(duration)),
///     )
///     .await
/// }
///
/// // Synchronous call:
/// let start = Instant::now();
/// let future = sleep::<Synchronous>(Duration::from_millis(100));
/// assert!(start.elapsed() <= Duration::from_millis(1));
/// future.get();
/// assert!(start.elapsed() >= Duration::from_millis(100));
///
/// // Asynchronous call:
/// # tokio::runtime::Builder::new_current_thread().enable_time().build().unwrap().block_on(async {
/// let start = Instant::now();
/// let future = sleep::<Asynchronous>(Duration::from_millis(100));
/// assert!(start.elapsed() <= Duration::from_millis(1));
/// future.await;
/// assert!(start.elapsed() >= Duration::from_millis(100));
/// # });
/// ```
///
/// This macro can also be used on traits and impls:
///
/// ```
/// # use async_if::{async_if, from_future, IsAsync, AsyncIf, Asynchronous, Synchronous};
/// # use std::time::Duration;
/// pub struct Std;
/// pub struct Tokio;
///
/// #[async_if(Self::A)]
/// pub trait Sleep {
///     type A: IsAsync;
///
///     async fn sleep(duration: Duration);
/// }
///
/// #[async_if(Self::A)]
/// impl Sleep for Std {
///     type A = Synchronous;
///
///     async fn sleep(duration: Duration) { std::thread::sleep(duration) }
/// }
///
/// #[async_if(Self::A)]
/// impl Sleep for Tokio {
///     type A = Asynchronous;
///
///     async fn sleep(duration: Duration) { from_future(tokio::time::sleep(duration)).await }
/// }
///
/// async_if::assert_sync(&Std::sleep(Duration::from_millis(100)));
/// async_if::assert_async(&Tokio::sleep(Duration::from_millis(100)));
/// ```
pub use async_if_macro::async_if;

/// Same as [`#[async_if]`](async_if), but accepts a bool condition instead of an [`IsAsync`] type.
pub use async_if_macro::async_when;

/// Same as the [`async move`](https://doc.rust-lang.org/stable/std/keyword.async.html) block, but
/// the result is an [`AsyncIf`] future inferred from the contents of the block.
///
/// # Example
///
/// ```
/// # use async_if::{Asynchronous, IsAsync, Synchronous, async_if, choose};
/// # use std::time::Duration;
/// # #[async_if(A)]
/// # async fn sleep<A: IsAsync>(duration: Duration) {
/// #     choose::<A, _>(
/// #         move || std::thread::sleep(duration),
/// #         move || Box::pin(tokio::time::sleep(duration)),
/// #     )
/// #     .await
/// # }
/// async_if::assert_async(&async_if::async_move! {
///     sleep::<Asynchronous>(Duration::from_millis(100)).await
/// });
///
/// async_if::assert_sync(&async_if::async_move! {
///     sleep::<Synchronous>(Duration::from_millis(100)).await
/// });
/// ```
///
/// `.await` expressions must either all be [`Synchronous`] or all be [`Asynchronous`]:
///
/// ```compile_fail
/// # use async_if::{Asynchronous, IsAsync, Synchronous, async_if, choose};
/// # use std::time::Duration;
/// # #[async_if(A)]
/// # async fn sleep<A: IsAsync>(duration: Duration) {
/// #     choose::<A, _>(
/// #         move || std::thread::sleep(duration),
/// #         move || Box::pin(tokio::time::sleep(duration)),
/// #     )
/// #     .await
/// # }
/// let _ = async_if::async_move! {
///    sleep::<Asynchronous>(Duration::from_millis(100)).await;
///    sleep::<Synchronous>(Duration::from_millis(100)).await;
/// };
/// ```
///
/// Incompabilities are detected at compile-time:
///
/// ```compile_fail
/// # use async_if::{Asynchronous, IsAsync, async_if, choose};
/// # use std::time::Duration;
/// # #[async_if(A)]
/// # async fn sleep<A: IsAsync>(duration: Duration) {
/// #     choose::<A, _>(
/// #         move || std::thread::sleep(duration),
/// #         move || Box::pin(tokio::time::sleep(duration)),
/// #     )
/// #     .await
/// # }
/// async_if::assert_sync(&async_if::async_move! {
///     sleep::<Asynchronous>(Duration::from_millis(100)).await
/// });
/// ```
///
/// ```compile_fail
/// # use async_if::{IsAsync, Synchronous, async_if, choose};
/// # use std::time::Duration;
/// # #[async_if(A)]
/// # async fn sleep<A: IsAsync>(duration: Duration) {
/// #     choose::<A, _>(
/// #         move || std::thread::sleep(duration),
/// #         move || Box::pin(tokio::time::sleep(duration)),
/// #     )
/// #     .await
/// # }
/// async_if::assert_async(&async_if::async_move! {
///     sleep::<Synchronous>(Duration::from_millis(100)).await
/// });
/// ```
///
/// ```compile_fail
/// # use std::time::Duration;
/// async_if::assert_async(&async_if::async_move! {
///     tokio::time::sleep(Duration::from_millis(100)).await
/// });
/// ```
pub use async_if_macro::async_move;

/// Same as the [`async`](https://doc.rust-lang.org/stable/std/keyword.async.html) block, but the
/// result is an [`AsyncIf`] future inferred from the contents of the block.
///
/// See [`async_move!`] for more information.
pub use async_if_macro::async_ref;

pub use futures::*;
use helpers::poll_expecting_ready;

mod private {
    /// Private trait which ensures that [`super::IsAsync`] can only be implemented in this crate.
    pub trait Sealed {}
}

/// Marker trait which defines whether a future is asynchronous or not.
///
/// Implemented by [`Asynchronous`] and [`Synchronous`].
pub trait IsAsync: private::Sealed + Copy + core::fmt::Debug + 'static {
    /// Whether the future is asynchronous or not.
    const IS_ASYNC: bool;
    /// The unique value which implements [`IsAsync`] with this value of [`Self::IS_ASYNC`].
    const VALUE: Self;
}

/// Marker type which implements [`IsAsync`] to determine whether a function should be performed
/// synchronously or asynchronously.
///
/// Redefined as [`Asynchronous`] and [`Synchronous`].
#[derive(Copy, Clone, Debug, Default)]
pub struct AsyncWhen<const IS_ASYNC: bool>;

/// Indicates that a function or future should execute asynchronously, possibly yielding when
/// awaiting on other futures.
pub type Asynchronous = AsyncWhen<true>;

/// Indicates that a function or future should execute synchronously, thus immediately returning a
/// value.
pub type Synchronous = AsyncWhen<false>;

impl<const IS_ASYNC: bool> private::Sealed for AsyncWhen<IS_ASYNC> {}

impl<const IS_ASYNC: bool> IsAsync for AsyncWhen<IS_ASYNC> {
    const IS_ASYNC: bool = IS_ASYNC;
    const VALUE: Self = Self;
}

/// Marker trait which is only implemented by [`Asynchronous`].
pub trait AsynchronousOnly: IsAsync {}
/// Marker trait which is only implemented by [`Synchronous`].
pub trait SynchronousOnly: IsAsync {}

impl AsynchronousOnly for Asynchronous {}
impl SynchronousOnly for Synchronous {}

/// A [`Future`] which may execute synchronously.
///
/// # Safety
///
/// Implementors of this trait must ensure that the future is always available synchronously if
/// `A` is [`Synchronous`].
pub unsafe trait AsyncIf<A: IsAsync>: Future {
    /// Returns the underlying "future" value without waiting.
    ///
    /// # Safety
    ///
    /// The caller must make sure that the future is not actually asynchronous.
    #[doc(hidden)]
    unsafe fn get_unchecked(self) -> Self::Output
    where
        Self: Sized;

    /// Returns the underlying "future" value.
    ///
    /// # Example
    ///
    /// ```
    /// # use async_if::{Asynchronous, AsyncIf, IsAsync, Synchronous, async_if};
    /// # use std::time::Duration;
    /// #[async_if(A)]
    /// async fn one_or_two<A: IsAsync>() -> u8 {
    ///     async_if::choose::<A, _>(
    ///         || 1,
    ///         || async { tokio::time::sleep(Duration::from_millis(1)).await; 2 },
    ///     )
    ///     .await
    /// }
    ///
    /// assert_eq!(one_or_two::<Synchronous>().get(), 1);
    /// ```
    ///
    /// Attempts to use this method on an asynchronous future will be caught at compile-time:
    ///
    /// ```compile_fail
    /// # use async_if::{Asynchronous, AsyncIf, IsAsync, Synchronous, async_if};
    /// # use std::time::Duration;
    /// # #[async_if(A)]
    /// # async fn one_or_two<A: IsAsync>() -> u8 {
    /// #     async_if::choose::<A, _>(
    /// #         || 1,
    /// #         || async { tokio::time::sleep(Duration::from_millis(1)).await; 2 },
    /// #     )
    /// #     .await
    /// # }
    /// assert_eq!(one::<Asynchronous>().get(), 2);
    /// ```
    fn get(self) -> Self::Output
    where
        Self: Sized,
        A: SynchronousOnly,
    {
        // SAFETY: `A` is `AlwaysSync`, so its result is always available synchronously.
        unsafe { self.get_unchecked() }
    }

    /// Returns the underlying "future" value without waiting if `A` is [`Synchronous`], and
    /// `self` otherwise.
    ///
    /// If `A` is known to be [`Synchronous`] at compile-time, prefer using [`AsyncIf::get()`].
    ///
    /// # Example
    ///
    /// ```
    /// # use async_if::{Asynchronous, AsyncIf, IsAsync, Synchronous, async_if};
    /// # use std::time::Duration;
    /// #[async_if(A)]
    /// async fn one_or_two<A: IsAsync>() -> u8 {
    ///     async_if::choose::<A, _>(
    ///         || 1,
    ///         || async { tokio::time::sleep(Duration::from_millis(1)).await; 2 },
    ///     )
    ///     .await
    /// }
    ///
    /// assert_eq!(one_or_two::<Synchronous>().try_get().ok(), Some(1));
    /// assert_eq!(one_or_two::<Asynchronous>().try_get().ok(), None);
    ///
    /// # tokio::runtime::Builder::new_current_thread().enable_time().build().unwrap().block_on(async {
    /// assert_eq!(one_or_two::<Synchronous>().await, 1);
    /// assert_eq!(one_or_two::<Asynchronous>().await, 2);
    /// # });
    /// ```
    fn try_get(self) -> Result<Self::Output, Self>
    where
        Self: Sized,
    {
        if A::IS_ASYNC {
            Err(self)
        } else {
            // SAFETY: `A::IS_ASYNC` is false in this branch.
            Ok(unsafe { self.get_unchecked() })
        }
    }

    /// Returns an [`AsyncIf`] future which preserves the [`IsAsync`] nature of the current future
    /// after mapping it using a matching function.
    ///
    /// If the input [`Future`] is [`Synchronous`], `map_sync` will be immediately called on its
    /// result and another [`Synchronous`] future will be returned.
    ///
    /// # Example
    ///
    /// ```
    /// # use async_if::{Asynchronous, AsyncIf, IsAsync, Synchronous, async_if};
    /// # use std::time::Duration;
    /// #[async_if(A)]
    /// async fn one_or_two<A: IsAsync>() -> u8 {
    ///     async_if::choose::<A, _>(|| 1, || async { 2 }).await
    /// }
    ///
    /// assert_eq!(
    ///     one_or_two::<Synchronous>().and_then(|x| x + 10, |x| async move { x.await + 20 }).get(),
    ///     11,
    /// );
    /// # tokio::runtime::Builder::new_current_thread().build().unwrap().block_on(async {
    /// assert_eq!(
    ///     one_or_two::<Asynchronous>().and_then(|x| x + 10, |x| async move { x.await + 20 }).await,
    ///     22,
    /// );
    /// # });
    /// ```
    ///
    /// `A` is preserved:
    ///
    /// ```compile_fail
    /// # use async_if::{Asynchronous, AsyncIf, IsAsync, Synchronous, async_if};
    /// # use std::time::Duration;
    /// # #[async_if(A)]
    /// # async fn one_or_two<A: IsAsync>() -> u8 {
    /// #     async_if::choose::<A, _>(|| 1, || async { 2 }).await
    /// # }
    /// assert_eq!(
    ///     one_or_two::<Asynchronous>().and_then(|x| x + 10, |x| async { x.await + 20 }).get(),
    ///     22,
    /// );
    /// ```
    fn and_then<F: Future>(
        self,
        map_sync: impl FnOnce(Self::Output) -> F::Output,
        map_async: impl FnOnce(Self) -> F,
    ) -> FutureIf<A, F>
    where
        Self: Sized,
    {
        match self.try_get() {
            Ok(value) => choose::<A, _>(
                move || map_sync(value),
                || unreachable!("bad AsyncIf impl: A::IS_ASYNC is true but try_get() returned Ok"),
            ),
            Err(future) => choose::<A, _>(
                || {
                    unreachable!(
                        "bad AsyncIf impl: A::IS_ASYNC is false but try_get() returned Err",
                    )
                },
                move || map_async(future),
            ),
        }
    }

    /// Returns an [`AsyncIf`] future which preserves the [`IsAsync`] nature of the current future.
    ///
    /// # Example
    ///
    /// ```
    /// # use async_if::{Asynchronous, AsyncIf, IsAsync, Synchronous, async_if};
    /// # use std::time::Duration;
    /// #[async_if(A)]
    /// async fn one_or_two<A: IsAsync>() -> u8 {
    ///     async_if::choose::<A, _>(|| 1, || async { 2 }).await
    /// }
    ///
    /// assert_eq!(one_or_two::<Synchronous>().map(|x| x + 1).get(), 2);
    /// # tokio::runtime::Builder::new_current_thread().build().unwrap().block_on(async {
    /// assert_eq!(one_or_two::<Asynchronous>().map(|x| x + 1).await, 3);
    /// # });
    /// ```
    ///
    /// `A` is preserved:
    ///
    /// ```compile_fail
    /// # use async_if::{Asynchronous, AsyncIf, IsAsync, Synchronous, async_if};
    /// # use std::time::Duration;
    /// # #[async_if(A)]
    /// # async fn one_or_two<A: IsAsync>() -> u8 {
    /// #     async_if::choose::<A, _>(|| 1, || async { 2 }).await
    /// # }
    /// assert_eq!(one_or_two::<Asynchronous>().map(|x| x + 1).get(), 3);
    /// ```
    fn map<T: Unpin>(self, map: impl FnOnce(Self::Output) -> T) -> impl AsyncIf<A, Output = T>
    where
        Self: Sized,
    {
        // We cannot reuse `and_then()` here because `map` cannot be copied into two closures at
        // once.
        match self.try_get() {
            Ok(value) => choose::<A, _>(
                move || map(value),
                || unreachable!("bad AsyncIf impl: A::IS_ASYNC is true but try_get() returned Ok"),
            ),
            Err(future) => choose::<A, _>(
                || {
                    unreachable!(
                        "bad AsyncIf impl: A::IS_ASYNC is false but try_get() returned Err",
                    )
                },
                move || async move { map(future.await) },
            ),
        }
    }
}

/// Alias of [`AsyncIf`] where a bool is specified rather than an [`IsAsync`] type.
pub trait AsyncIfConst<const IS_ASYNC: bool>: AsyncIf<AsyncWhen<IS_ASYNC>> {}

impl<const IS_ASYNC: bool, F: AsyncIf<AsyncWhen<IS_ASYNC>>> AsyncIfConst<IS_ASYNC> for F {}

/// Asserts at compile-time that an [`AsyncIf`] future is [`Asynchronous`].
///
/// # Example
///
/// ```
/// # use async_if::{Asynchronous, IsAsync, async_if, assert_async};
/// #[async_if(A)]
/// async fn one<A: IsAsync>() -> u8 {
///     async_if::choose::<A, _>(|| 1, || async { 1 }).await
/// }
///
/// assert_async(&one::<Asynchronous>());
/// ```
///
/// Assertions happen at compile-time:
///
/// ```compile_fail
/// # use async_if::{Synchronous, IsAsync, async_if, assert_async};
/// # #[async_if(A)]
/// # async fn one<A: IsAsync>() -> u8 {
/// #     async_if::choose::<A, _>(|| 1, || async { 1 }).await
/// # }
/// assert_async(&one::<Synchronous>());
/// ```
pub const fn assert_async<F: AsyncIf<Asynchronous>>(_: &F) {}

/// Asserts at compile-time that an [`AsyncIf`] future is [`Synchronous`].
///
/// # Example
///
/// ```
/// # use async_if::{Synchronous, IsAsync, async_if, assert_sync};
/// #[async_if(A)]
/// async fn one<A: IsAsync>() -> u8 {
///     async_if::choose::<A, _>(|| 1, || async { 1 }).await
/// }
///
/// assert_sync(&one::<Synchronous>());
/// ```
///
/// Assertions happen at compile-time:
///
/// ```compile_fail
/// # use async_if::{Asynchronous, IsAsync, async_if, assert_sync};
/// # #[async_if(A)]
/// # async fn one<A: IsAsync>() -> u8 {
/// #     async_if::choose::<A, _>(|| 1, || async { 1 }).await
/// # }
/// assert_sync(&one::<Asynchronous>());
/// ```
pub const fn assert_sync<F: AsyncIf<Synchronous>>(_: &F) {}

/// Returns `future` as-is. Used to automatically infer the [`IsAsync`] type parameter from an
/// expression in macro-expanded code.
#[doc(hidden)]
pub const fn infer_with<A: IsAsync, F: AsyncIf<A>>(future: F, _: PhantomData<A>) -> F {
    future
}

// SAFETY: `core::future::Ready` always completes immediately.
unsafe impl<A: IsAsync, T> AsyncIf<A> for core::future::Ready<T> {
    unsafe fn get_unchecked(self) -> Self::Output
    where
        Self: Sized,
    {
        poll_expecting_ready(self).expect("Ready::poll() returned Poll::Pending")
    }
}
