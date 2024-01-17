use core::{
    future::Future,
    task::{Context, Poll, Waker},
};

/// Stable version of [`Waker::noop()`](
/// https://doc.rust-lang.org/stable/std/task/struct.Waker.html#method.noop).
fn noop_waker() -> Waker {
    use core::task::{RawWaker, RawWakerVTable};

    const VTABLE: RawWakerVTable = RawWakerVTable::new(|_| RAW, |_| {}, |_| {}, |_| {});
    const RAW: RawWaker = RawWaker::new(core::ptr::null(), &VTABLE);

    // SAFETY: all operations are no-op, so we can't do anything unsafe.
    unsafe { Waker::from_raw(RAW) }
}

/// Polls the given future, expecting it to return [`Poll::Ready`], returning [`None`] if it
/// doesn't.
pub fn poll_expecting_ready<F: Future>(future: F) -> Option<F::Output> {
    let future = core::pin::pin!(future);
    let waker = noop_waker();
    let mut context = Context::from_waker(&waker);

    match future.poll(&mut context) {
        Poll::Ready(value) => Some(value),
        Poll::Pending => None,
    }
}
