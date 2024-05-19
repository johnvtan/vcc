#ifndef VCC_VEC_H
#define VCC_VEC_H

#include <stddef.h>
#include <stdint.h>

typedef struct {
  // Number of items currently in the vector
  size_t len;

  // Max number of items that could be stored
  // in the vector before reallocating.
  size_t cap;

  // Size of each item in bytes.
  // It's assumed in the functions below that all
  // void* parameters contain at least item_size bytes.
  size_t item_size;

  // Allocated memory containing items.
  char* data;
} Vec;

#define VEC_INIT_CAP (16U)

// Creates a new vector with the given item_size
// and an initial capacity of VEC_INIT_CAP.
Vec* vec_new(size_t item_size);

// Creates a new vector with the given item_size
// and an initial capacity.
Vec* vec_new_cap(size_t item_size, size_t cap);

// Initializes a vector
void vec_init(Vec* v, size_t item_size);

// Initializes a new vector with given capacity.
void vec_init_cap(Vec* v, size_t item_size, size_t cap);

// Pushes an item onto the end of the vector, reallocating
// if necessary.
// The item is copied into the vector.
void vec_push(Vec* vec, void* item);

// Adds a new empty item onto the vector and returns a pointer
// to that item
void* vec_push_empty(Vec* vec);

// Removes the last item from the vector.
void vec_pop(Vec* vec);

// Returns a pointer to the nth item in the vector.
// The returned item is owned by `vec`.
void* vec_get(const Vec* vec, size_t n);

// Returns a pointer to the last item in the vector.
// The returned item is owned by `vec`.
void* vec_back(Vec* vec);

// Overwrites the nth item in the vector with item.
// item is copied into the vector.
void vec_set(Vec* vec, size_t n, void* item);

// Concatenates v2 onto the end of v1
void vec_concat(Vec* v1, Vec* v2);

// Macro for iterating over the elements of a vector.
// Creates a loop variable called |iter| that contains a pointer to the item
// and the current index |iter.i|.
// The user defines the name of the item in |iter| through the |item| parameter.
#define vec_for_each(vec, item_type, item)                                 \
  for (                                                                    \
      struct {                                                             \
        size_t i;                                                          \
        item_type* item;                                                   \
      } iter = {0, vec_get(vec, 0)};                                       \
      iter.i < vec->len; ++iter.i,                                         \
        iter.item = (iter.i < vec->len) ? (item_type*)vec_get(vec, iter.i) \
                                        : NULL)

#endif
