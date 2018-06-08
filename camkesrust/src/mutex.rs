//
// Copyright 2018, Data61
// Commonwealth Scientific and Industrial Research Organisation (CSIRO)
// ABN 41 687 119 230.
//
// This software may be distributed and modified according to the terms of
// the BSD 2-Clause license. Note that NO WARRANTY is provided.
// See "LICENSE_BSD2.txt" for details.
//
// @TAG(DATA61_BSD)
//
use core::ops::{Drop, Deref, DerefMut};
use core::cell::UnsafeCell;

use libc::c_void;

extern "C"
{
    /// These functions are provided by libsel4camkes: <camkes/sync.h>
    /// They provide an allocation and locking interface for mutexes backed by seL4 Notification objects.
    /// These functions are not thread safe and must be handled as such.

    /// Allocate a new mutex. Returns 0 on success, -1 on failure
    fn camkes_mutex_new(allocator: *mut c_void, mutex: *mut*mut c_void) -> isize;

    /// Acquire lock to mutex. Cannot be called if lock is held by current thread.
    fn camkes_mutex_lock(mutex: *mut c_void) -> isize;

    /// Release lock to mutex. Can only be called if current thread holds lock.
    fn camkes_mutex_unlock(mutex: *mut c_void) -> isize;

    /// Releases mutex back to allocator.
    fn camkes_mutex_free(allocator: *mut c_void, mutex: *mut c_void) -> isize;

    /// Initialises allocator.
    fn init_default_allocator_heap(allocator: *mut*mut c_void) -> isize;
}

// Reference to allocator returned by initial call to `init_default_allocator_heap`.
// We bootstrap a Mutex to store the allocator in so that subsequent calls to it are
// synchronised.  It cannot be used until `init_allocator` has been called.
static mut ALLOCATOR: Mutex<*mut c_void> = Mutex::uninitialized(0 as *mut c_void);



/// Mutual Exclusion provided by mutex_pool in libsel4camkes c library.
pub struct Mutex<T: ?Sized>
{
    lock: *mut c_void,
    data: UnsafeCell<T>,
}


pub struct MutexGuard<'a, T: ?Sized + 'a>
{
    lock: *mut c_void,
    data: &'a mut T,
}

// Same unsafe impls as `std::sync::Mutex`
unsafe impl<T: ?Sized + Send> Sync for Mutex<T> {}
unsafe impl<T: ?Sized + Send> Send for Mutex<T> {}

impl<T> Mutex<T>
{

    /// This function needs to be called in a single threaded environment such as the
    /// Camkes `pre_init` function.  If you are using lazy_static! then this needs to
    /// be called before any of the lazy initialisation occurs.
    ///
    /// TODO: This could potentially be moved to a `lazy_static!` macro that initialises ALLOCATOR
    pub unsafe fn init_allocator() -> Result<(),()>
    {

        // Initialise allocator in underlying c library
        let mut alloc = 0 as *mut c_void;
        match init_default_allocator_heap(&mut alloc) {
            0 => (),
            _ => panic!{"Could not allocate default allocator"},
        }

        // Use allocator to create initial mutex for future accesses to the allocator
        // by calls to `Mutex::new(T)`.
        let mut mtx = 0 as *mut c_void;
        match camkes_mutex_new(alloc, &mut mtx) {
            0 => (),
            _ => panic!{"Could not allocate inital mutex for allocator."},
        }

        // Save reference to allocator in static mut. The mutex should ensure accesses
        // are thread safe.
        ALLOCATOR = Mutex{
            lock:mtx,
            data:UnsafeCell::new(alloc)
        };
        Ok(())
    }

    /// const initialiser for bootstrapping ALLOCATOR.
    const fn uninitialized(user_data: T) -> Mutex<T> {
        Mutex { lock: 0 as *mut c_void, data: UnsafeCell::new(user_data) }
    }

    /// Create a new Mutex around data T. Returns an error code passed from the underlying
    /// library if error.
    pub fn new(user_data: T) -> Result<Mutex<T>, isize>
    {

        let mut mtx = 0 as *mut c_void;
        unsafe {
            let alloc = ALLOCATOR.lock();
            match camkes_mutex_new(*alloc, &mut mtx) {
                0 => (),
                i => return Err(i),
            }
        };
        Ok(Mutex
        {
            lock: mtx,
            data: UnsafeCell::new(user_data),
        })
    }


    /// Consumes this mutex, returning the underlying data.
    pub fn into_inner(self) -> T
    {
        // We know statically that there are no outstanding references to
        // `self` so there's no need to lock.
        let Mutex { data, lock } = self;
        unsafe {
            let alloc = ALLOCATOR.lock();
            match camkes_mutex_free(*alloc, lock) {
                0 => (),
                _ => panic!{"Failed to free mutex"}
            }
        };
        data.into_inner()
    }
}

impl<T: ?Sized> Mutex<T>
{

    /// Acquire lock. camkes_mutex_lock is blocking until the lock is acquired.
    /// There is no way to timeout on a lock request.
    pub fn lock(&self) -> MutexGuard<T>
    {
        unsafe {
            match camkes_mutex_lock(self.lock) {
                0 => (),
                _ => panic!{"lock returned error"},
            }
        };
        MutexGuard
        {
            lock: self.lock,
            data: unsafe { &mut *self.data.get() },
        }
    }
}

// Implement some standard Deref coercions
impl<'a, T: ?Sized> Deref for MutexGuard<'a, T>
{
    type Target = T;
    fn deref<'b>(&'b self) -> &'b T { &*self.data }
}

impl<'a, T: ?Sized> DerefMut for MutexGuard<'a, T>
{
    fn deref_mut<'b>(&'b mut self) -> &'b mut T { &mut *self.data }
}

impl<'a, T: ?Sized> Drop for MutexGuard<'a, T>
{
    /// The dropping of the MutexGuard will release the lock it was created from.
    fn drop(&mut self)
    {
        unsafe{
            match camkes_mutex_unlock(self.lock) {
                0 => (),
                _ => panic!{"Failed to release lock"},
            }
        };
    }
}
