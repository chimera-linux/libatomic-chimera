// this is an implementation of libatomic created for Chimera Linux
//
// based on atomic.c from llvm's compiler-rt builtins
//
// missing implementations were filled in, some parts were rewritten
//
// changes by q66 <q66@chimera-linux.org>
//
// provided under the same license as llvm (apache-2.0)
//
// original header follows:
//
//===-- atomic.c - Implement support functions for atomic operations.------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
//  atomic.c defines a set of functions for performing atomic accesses on
//  arbitrary-sized memory locations.  This design uses locks that should
//  be fast in the uncontended case, for two reasons:
//
//  1) This code must work with C programs that do not link to anything
//     (including pthreads) and so it should not depend on any pthread
//     functions.
//  2) Atomic operations, rather than explicit mutexes, are most commonly used
//     on code where contended operations are rate.
//
//  To avoid needing a per-object lock, this code allocates an array of
//  locks and hashes the object pointers to find the one that it should use.
//  For operations that must be atomic on two locations, the lower lock is
//  always acquired first, to avoid deadlock.
//
//===----------------------------------------------------------------------===//

#include <stdbool.h>
#include <string.h>
#include <stddef.h>
#include <stdint.h>
#include <fenv.h>

#define SPINLOCK_COUNT (1 << 10)

static const long SPINLOCK_MASK = SPINLOCK_COUNT - 1;

/// lock implementation; clear and tas are guaranteed to be lock free

typedef bool lock_t;

static inline __attribute__((always_inline)) void unlock(lock_t *l) {
  __atomic_clear(l, __ATOMIC_RELEASE);
}

static inline __attribute__((always_inline)) void lock(lock_t *l) {
  while (__atomic_test_and_set(l, __ATOMIC_ACQUIRE));
}

static lock_t locks[SPINLOCK_COUNT];

static inline __attribute__((always_inline)) lock_t *lock_for_pointer(void *ptr) {
  intptr_t hash = (intptr_t)ptr;
  // Disregard the lowest 4 bits.  We want all values that may be part of the
  // same memory operation to hash to the same value and therefore use the same
  // lock.
  hash >>= 4;
  // Use the next bits as the basis for the hash
  intptr_t low = hash & SPINLOCK_MASK;
  // Now use the high(er) set of bits to perturb the hash, so that we don't
  // get collisions from atomic fields in a single object
  hash >>= 16;
  hash ^= low;
  // Return a pointer to the word to use
  return locks + (hash & SPINLOCK_MASK);
}

/// Macros for determining whether a size is lock free.
#define ATOMIC_ALWAYS_LOCK_FREE_OR_ALIGNED_LOCK_FREE(size, p)                  \
  (__atomic_always_lock_free(size, p) ||                                       \
   (__atomic_always_lock_free(size, 0) && ((uintptr_t)p % size) == 0))

#define IS_LOCK_FREE_1(p) ATOMIC_ALWAYS_LOCK_FREE_OR_ALIGNED_LOCK_FREE(1, p)
#define IS_LOCK_FREE_2(p) ATOMIC_ALWAYS_LOCK_FREE_OR_ALIGNED_LOCK_FREE(2, p)
#define IS_LOCK_FREE_4(p) ATOMIC_ALWAYS_LOCK_FREE_OR_ALIGNED_LOCK_FREE(4, p)
#define IS_LOCK_FREE_8(p) ATOMIC_ALWAYS_LOCK_FREE_OR_ALIGNED_LOCK_FREE(8, p)
#define IS_LOCK_FREE_16(p) ATOMIC_ALWAYS_LOCK_FREE_OR_ALIGNED_LOCK_FREE(16, p)

/// Macro that calls the compiler-generated lock-free versions of functions
/// when they exist.
#define TRY_LOCK_FREE_CASE(n, type, ptr)                                       \
  case n:                                                                      \
    if (IS_LOCK_FREE_##n(ptr)) {                                               \
      LOCK_FREE_ACTION(type);                                                  \
    }                                                                          \
    break;
#ifdef __SIZEOF_INT128__
#define TRY_LOCK_FREE_CASE_16(p) TRY_LOCK_FREE_CASE(16, __uint128_t, p)
#else
#define TRY_LOCK_FREE_CASE_16(p) /* __uint128_t not available */
#endif

#define LOCK_FREE_CASES(ptr)                                                   \
  do {                                                                         \
    switch (size) {                                                            \
      TRY_LOCK_FREE_CASE(1, uint8_t, ptr)                                      \
      TRY_LOCK_FREE_CASE(2, uint16_t, ptr)                                     \
      TRY_LOCK_FREE_CASE(4, uint32_t, ptr)                                     \
      TRY_LOCK_FREE_CASE(8, uint64_t, ptr)                                     \
      TRY_LOCK_FREE_CASE_16(ptr) /* __uint128_t may not be supported */        \
    default:                                                                   \
      break;                                                                   \
    }                                                                          \
  } while (0)

/// Whether atomic operations for the given size (and alignment) are lock-free.
#pragma redefine_extname __atomic_is_lock_free_c __atomic_is_lock_free
bool __atomic_is_lock_free_c(size_t size, void *ptr) {
#define LOCK_FREE_ACTION(type) return true;
  LOCK_FREE_CASES(ptr);
#undef LOCK_FREE_ACTION
  return false;
}

/// An atomic load operation.  This is atomic with respect to the source
/// pointer only.
#pragma redefine_extname __atomic_load_c __atomic_load
void __atomic_load_c(int size, void *src, void *dest, int model) {
#define LOCK_FREE_ACTION(type)                                                 \
  *((type *)dest) = __atomic_load_n((type *)src, model);                        \
  return;
  LOCK_FREE_CASES(src);
#undef LOCK_FREE_ACTION
  lock_t *l = lock_for_pointer(src);
  lock(l);
  memcpy(dest, src, size);
  unlock(l);
}

/// An atomic store operation.  This is atomic with respect to the destination
/// pointer only.
#pragma redefine_extname __atomic_store_c __atomic_store
void __atomic_store_c(int size, void *dest, void *src, int model) {
#define LOCK_FREE_ACTION(type)                                                 \
  __atomic_store_n((type *)dest, *(type *)src, model);                         \
  return;
  LOCK_FREE_CASES(dest);
#undef LOCK_FREE_ACTION
  lock_t *l = lock_for_pointer(dest);
  lock(l);
  memcpy(dest, src, size);
  unlock(l);
}

/// Atomic compare and exchange operation.  If the value at *ptr is identical
/// to the value at *expected, then this copies value at *desired to *ptr.  If
/// they  are not, then this stores the current value from *ptr in *expected.
///
/// This function returns 1 if the exchange takes place or 0 if it fails.
#pragma redefine_extname __atomic_compare_exchange_c __atomic_compare_exchange
int __atomic_compare_exchange_c(int size, void *ptr, void *expected,
                                void *desired, int success, int failure) {
#define LOCK_FREE_ACTION(type)                                                 \
  return __atomic_compare_exchange_n(                                          \
      (type *)ptr, (type *)expected, *(type *)desired, 0, success,             \
      failure)
  LOCK_FREE_CASES(ptr);
#undef LOCK_FREE_ACTION
  lock_t *l = lock_for_pointer(ptr);
  lock(l);
  if (memcmp(ptr, expected, size) == 0) {
    memcpy(ptr, desired, size);
    unlock(l);
    return 1;
  }
  memcpy(expected, ptr, size);
  unlock(l);
  return 0;
}

/// Performs an atomic exchange operation between two pointers.  This is atomic
/// with respect to the target address.
#pragma redefine_extname __atomic_exchange_c __atomic_exchange
void __atomic_exchange_c(int size, void *ptr, void *val, void *old, int model) {
#define LOCK_FREE_ACTION(type)                                                 \
  *(type *)old =                                                               \
      __atomic_exchange_n((type *)ptr, *(type *)val, model);                   \
  return;
  LOCK_FREE_CASES(ptr);
#undef LOCK_FREE_ACTION
  lock_t *l = lock_for_pointer(ptr);
  lock(l);
  memcpy(old, ptr, size);
  memcpy(ptr, val, size);
  unlock(l);
}

////////////////////////////////////////////////////////////////////////////////
// Where the size is known at compile time, the compiler may emit calls to
// specialised versions of the above functions.
////////////////////////////////////////////////////////////////////////////////
#ifdef __SIZEOF_INT128__
#define OPTIMISED_CASES                                                        \
  OPTIMISED_CASE(1, IS_LOCK_FREE_1, uint8_t)                                   \
  OPTIMISED_CASE(2, IS_LOCK_FREE_2, uint16_t)                                  \
  OPTIMISED_CASE(4, IS_LOCK_FREE_4, uint32_t)                                  \
  OPTIMISED_CASE(8, IS_LOCK_FREE_8, uint64_t)                                  \
  OPTIMISED_CASE(16, IS_LOCK_FREE_16, __uint128_t)
#else
#define OPTIMISED_CASES                                                        \
  OPTIMISED_CASE(1, IS_LOCK_FREE_1, uint8_t)                                   \
  OPTIMISED_CASE(2, IS_LOCK_FREE_2, uint16_t)                                  \
  OPTIMISED_CASE(4, IS_LOCK_FREE_4, uint32_t)                                  \
  OPTIMISED_CASE(8, IS_LOCK_FREE_8, uint64_t)
#endif

#define OPTIMISED_CASE(n, lockfree, type)                                      \
  type __atomic_load_##n(type *src, int model) {                               \
    if (lockfree(src))                                                         \
      return __atomic_load_n(src, model);                                      \
    lock_t *l = lock_for_pointer(src);                                         \
    lock(l);                                                                   \
    type val = *src;                                                           \
    unlock(l);                                                                 \
    return val;                                                                \
  }
OPTIMISED_CASES
#undef OPTIMISED_CASE

#define OPTIMISED_CASE(n, lockfree, type)                                      \
  void __atomic_store_##n(type *dest, type val, int model) {                   \
    if (lockfree(dest)) {                                                      \
      __atomic_store_n(dest, val, model);                                      \
      return;                                                                  \
    }                                                                          \
    lock_t *l = lock_for_pointer(dest);                                        \
    lock(l);                                                                   \
    *dest = val;                                                               \
    unlock(l);                                                                 \
    return;                                                                    \
  }
OPTIMISED_CASES
#undef OPTIMISED_CASE

#define OPTIMISED_CASE(n, lockfree, type)                                      \
  type __atomic_exchange_##n(type *dest, type val, int model) {                \
    if (lockfree(dest))                                                        \
      return __atomic_exchange_n(dest, val, model);                            \
    lock_t *l = lock_for_pointer(dest);                                        \
    lock(l);                                                                   \
    type tmp = *dest;                                                          \
    *dest = val;                                                               \
    unlock(l);                                                                 \
    return tmp;                                                                \
  }
OPTIMISED_CASES
#undef OPTIMISED_CASE

#define OPTIMISED_CASE(n, lockfree, type)                                      \
  bool __atomic_compare_exchange_##n(type *ptr, type *expected, type desired,  \
                                     int success, int failure) {               \
    if (lockfree(ptr))                                                         \
      return __atomic_compare_exchange_n(                                      \
          ptr, expected, desired, 0, success, failure);                        \
    lock_t *l = lock_for_pointer(ptr);                                         \
    lock(l);                                                                   \
    if (*ptr == *expected) {                                                   \
      *ptr = desired;                                                          \
      unlock(l);                                                               \
      return true;                                                             \
    }                                                                          \
    *expected = *ptr;                                                          \
    unlock(l);                                                                 \
    return false;                                                              \
  }
OPTIMISED_CASES
#undef OPTIMISED_CASE

////////////////////////////////////////////////////////////////////////////////
// Atomic read-modify-write operations for integers of various sizes.
////////////////////////////////////////////////////////////////////////////////
#define ATOMIC_RMW(n, lockfree, type, opname, op)                              \
  type __atomic_fetch_##opname##_##n(type *ptr, type val, int model) {         \
    if (lockfree(ptr))                                                         \
      return __atomic_fetch_##opname(ptr, val, model);                         \
    lock_t *l = lock_for_pointer(ptr);                                         \
    lock(l);                                                                   \
    type tmp = *ptr;                                                           \
    *ptr = tmp op val;                                                         \
    unlock(l);                                                                 \
    return tmp;                                                                \
  }                                                                            \
                                                                               \
  type __atomic_##opname##_fetch_##n(type *ptr, type val, int model) {         \
    if (lockfree(ptr))                                                         \
      return __atomic_##opname##_fetch(ptr, val, model);                       \
    lock_t *l = lock_for_pointer(ptr);                                         \
    lock(l);                                                                   \
    type tmp = *ptr;                                                           \
    tmp = tmp op val;                                                          \
    *ptr = tmp;                                                                \
    unlock(l);                                                                 \
    return tmp;                                                                \
  }

#define ATOMIC_RMW_NAND(n, lockfree, type)                                     \
  type __atomic_fetch_nand_##n(type *ptr, type val, int model) {               \
    if (lockfree(ptr))                                                         \
      return __atomic_fetch_nand(ptr, val, model);                             \
    lock_t *l = lock_for_pointer(ptr);                                         \
    lock(l);                                                                   \
    type tmp = *ptr;                                                           \
    *ptr = ~(tmp & val);                                                       \
    unlock(l);                                                                 \
    return tmp;                                                                \
  }                                                                            \
                                                                               \
  type __atomic_nand_fetch_##n(type *ptr, type val, int model) {               \
    if (lockfree(ptr))                                                         \
      return __atomic_nand_fetch(ptr, val, model);                             \
    lock_t *l = lock_for_pointer(ptr);                                         \
    lock(l);                                                                   \
    type tmp = *ptr;                                                           \
    tmp = ~(tmp & val);                                                        \
    *ptr = tmp;                                                                \
    unlock(l);                                                                 \
    return tmp;                                                                \
  }

#define ATOMIC_TAS(n, lockfree, type)                                          \
  bool __atomic_test_and_set_##n(type *ptr, int model) {                       \
    if (lockfree(ptr))                                                         \
      return __atomic_test_and_set(ptr, model);                                \
    lock_t *l = lock_for_pointer(ptr);                                         \
    lock(l);                                                                   \
    type tmp = *ptr;                                                           \
    *ptr = 1;                                                                  \
    unlock(l);                                                                 \
    return !!tmp;                                                              \
  }

#define OPTIMISED_CASE(n, lockfree, type) ATOMIC_RMW(n, lockfree, type, add, +)
OPTIMISED_CASES
#undef OPTIMISED_CASE
#define OPTIMISED_CASE(n, lockfree, type) ATOMIC_RMW(n, lockfree, type, sub, -)
OPTIMISED_CASES
#undef OPTIMISED_CASE
#define OPTIMISED_CASE(n, lockfree, type) ATOMIC_RMW(n, lockfree, type, and, &)
OPTIMISED_CASES
#undef OPTIMISED_CASE
#define OPTIMISED_CASE(n, lockfree, type) ATOMIC_RMW(n, lockfree, type, or, |)
OPTIMISED_CASES
#undef OPTIMISED_CASE
#define OPTIMISED_CASE(n, lockfree, type) ATOMIC_RMW(n, lockfree, type, xor, ^)
OPTIMISED_CASES
#undef OPTIMISED_CASE
#define OPTIMISED_CASE(n, lockfree, type) ATOMIC_RMW_NAND(n, lockfree, type)
OPTIMISED_CASES
#undef OPTIMISED_CASE
#define OPTIMISED_CASE(n, lockfree, type) ATOMIC_TAS(n, lockfree, type)
OPTIMISED_CASES
#undef OPTIMISED_CASE

/* atomic_flag */

typedef struct atomic_flag { bool v; } atomic_flag;

void atomic_flag_clear(volatile atomic_flag *o) {
    __atomic_clear(&o->v, __ATOMIC_SEQ_CST);
}

void atomic_flag_clear_explicit(volatile atomic_flag *o, int model) {
    __atomic_clear(&o->v, model);
}

bool atomic_flag_test_and_set(volatile atomic_flag *o) {
    return __atomic_test_and_set(&o->v, __ATOMIC_SEQ_CST);
}

bool atomic_flag_test_and_set_explicit(volatile atomic_flag *o, int model) {
    return __atomic_test_and_set(&o->v, model);
}

/* fence */

void atomic_thread_fence(int model) {
    __atomic_thread_fence(model);
}

void atomic_signal_fence(int model) {
    __atomic_signal_fence(model);
}

/* provided by gcc libatomic */

void __atomic_feraiseexcept(int e) {
    volatile float r __attribute__((unused));
#ifdef FE_INVALID
    if (e & FE_INVALID) {
        volatile float z = 0.0f;
        r = z / z;
    }
#endif
#ifdef FE_DIVBYZERO
    if (e & FE_DIVBYZERO) {
        volatile float z = 0.0f;
        r = 1.0f / z;
    }
#endif
#ifdef FE_OVERFLOW
    if (e & FE_OVERFLOW) {
        volatile float m = __FLT_MAX__;
        r = m * m;
    }
#endif
#ifdef FE_UNDERFLOW
    if (e & FE_UNDERFLOW) {
        volatile float m = __FLT_MIN__;
        r = m * m;
    }
#endif
#ifdef FE_INEXACT
    if (e & FE_INEXACT) {
        volatile float t = 3.0f;
        r = 1.0f / t;
    }
#endif
}
