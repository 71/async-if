use core::time::Duration;

async_trait! {
    /// Time-related methods.
    pub trait Time {
        /// Sleeps for the given duration.
        ///
        /// # Implementations
        ///
        /// - `std`: [`std::thread::sleep()`]
        /// - `async-std`: [`async_std::task::sleep()`]
        /// - `tokio`: [`tokio::time::sleep()`]
        async fn sleep(duration: Duration) {
            match Self {
                "std" => std::thread::sleep(duration),
                "async-std" => async_std::task::sleep(duration).await,
                "tokio" => tokio::time::sleep(duration).await,
            }
        }
    }

    impl for "std", "async-std", "tokio" if "tokio-time";
}

test_all! {
    async fn test_sleep<T: Time in (Std, AsyncStd, Tokio)>() {
        let time_before = std::time::Instant::now();
        T::sleep(Duration::from_secs(1)).await;
        assert!(time_before.elapsed() >= Duration::from_secs(1));
    }
}
