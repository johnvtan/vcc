#include <assert.h>
#include <stdio.h>
#include <vcc/vec.h>

int main(void) {
  Vec* vec = vec_new(sizeof(size_t));
  assert(vec->len == 0 && vec->cap == VEC_INIT_CAP);

  size_t* n;

  for (size_t i = 0; i < 10000; i++) {
    assert(vec->cap >= vec->len);
    assert(vec->len == i);
    vec_push(vec, &i);

    n = vec_back(vec);
    assert(*n == i);
  }

  assert(vec->len == 10000);
  assert(vec->cap == (1 << 14));

  for (size_t i = 0; i < 10000; i++) {
    n = vec_get(vec, i);
    assert(*n == i);
  }

  for (size_t i = 0; i < 10000; i++) {
    size_t n2 = i * 2;
    vec_set(vec, i, &n2);

    n = vec_get(vec, i);
    assert(n2 == *n);
  }

  for (size_t i = 9999; i > 0; i--) {
    vec_pop(vec);
    assert(vec->len == i);
  }

  vec_pop(vec);
  assert(vec->len == 0);

  // concat test
  Vec* v1 = vec_new(sizeof(size_t));
  Vec* v2 = vec_new(sizeof(size_t));
  for (size_t i = 0; i < 10000; i++) {
    vec_push(v1, &i);
  }

  for (size_t i = 10000; i < 20000; i++) {
    vec_push(v2, &i);
  }

  vec_concat(v1, v2);

  for (size_t i = 0; i < 20000; i++) {
    n = vec_get(v1, i);
    assert(i == *n);
  }

  printf("tests pass\n");
  return 0;
}
