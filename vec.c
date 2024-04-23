#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <vcc/vec.h>

static inline size_t data_idx(const Vec* vec, size_t idx) {
  return idx * vec->item_size;
}

static inline char* get_item(const Vec* vec, size_t item_idx) {
  return &vec->data[data_idx(vec, item_idx)];
}

static inline bool full(Vec* vec) { return vec->cap == vec->len; }

static void double_cap(Vec* vec) {
  vec->cap *= 2;
  vec->data = realloc(vec->data, vec->cap * vec->item_size);
  assert(vec->data);
}

Vec* vec_new(size_t item_size) {
  Vec* ret = calloc(1, sizeof(Vec));
  vec_init(ret, item_size);
  return ret;
}

Vec* vec_new_cap(size_t item_size, size_t cap) {
  Vec* ret = calloc(1, sizeof(Vec));
  vec_init_cap(ret, item_size, cap);
  return ret;
}

void vec_init(Vec* v, size_t item_size) {
  vec_init_cap(v, item_size, VEC_INIT_CAP);
}

void vec_init_cap(Vec* v, size_t item_size, size_t cap) {
  assert(v && item_size && cap);
  v->cap = cap;
  v->item_size = item_size;
  v->data = calloc(v->cap, v->item_size);
  assert(v->data);
}

void* vec_push_empty(Vec* vec) {
  assert(vec && vec->data);
  if (full(vec)) double_cap(vec);

  assert(!full(vec));

  char* next = get_item(vec, vec->len);
  vec->len++;
  return next;
}

void vec_push(Vec* vec, void* item) {
  char* next = vec_push_empty(vec);
  memcpy(next, item, vec->item_size);
}

void vec_pop(Vec* vec) {
  assert(vec && vec->data && vec->len);
  vec->len--;
}

void* vec_get(const Vec* vec, size_t n) {
  assert(vec && n < vec->len);
  return get_item(vec, n);
}

void* vec_back(Vec* vec) {
  assert(vec);
  if (vec->len) return get_item(vec, vec->len - 1);
  return NULL;
}

void vec_set(Vec* vec, size_t n, void* item) {
  assert(vec && vec->data && n < vec->len && item);
  char* ptr = get_item(vec, n);
  memcpy(ptr, item, vec->item_size);
}

void vec_concat(Vec* v1, Vec* v2) {
  assert(v1->item_size == v2->item_size);
  for (size_t i = 0; i < v2->len; i++) {
    vec_push(v1, vec_get(v2, i));
  }
}
