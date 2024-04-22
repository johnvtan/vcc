#include <assert.h>
#include <stdio.h>
#include <vcc/hashmap.h>
#include <vcc/string.h>

int main(void) {
  Hashmap* h = hashmap_new();

  for (size_t i = 1; i < 10000; i++) {
    String* key = string_format("key %lu", i);
    hashmap_put(h, key, (void*)i);
    void* val = hashmap_get(h, key);
    assert((size_t)val == i);
  }

  for (size_t i = 2000; i < 3000; i++) {
    String* key = string_format("key %lu", i);
    hashmap_del(h, key);
    assert(hashmap_get(h, key) == NULL);
  }

  for (size_t i = 10000; i < 15000; i++) {
    String* key = string_format("key %lu", i);
    hashmap_put(h, key, (void*)i);
    void* val = hashmap_get(h, key);
    assert((size_t)val == i);
  }

  for (size_t i = 12345; i < 14567; i++) {
    String* key = string_format("key %lu", i);
    hashmap_del(h, key);
    assert(hashmap_get(h, key) == NULL);
  }

  for (size_t i = 13000; i < 14000; i++) {
    String* key = string_format("key %lu", i);
    hashmap_put(h, key, (void*)i);
    assert((size_t)hashmap_get(h, key) == i);
  }

  for (size_t i = 15000; i < 50000; i++) {
    String* key = string_format("key %lu", i);
    hashmap_put(h, key, (void*)i);
    assert((size_t)hashmap_get(h, key) == i);
  }

  for (size_t i = 1; i < 50000; i++) {
    String* key = string_format("key %lu", i);
    void* val = hashmap_get(h, key);

    if ((i >= 2000 && i < 3000) || (i >= 12345 && i < 13000) ||
        (i >= 14000 && i < 14567)) {
      assert(val == NULL);
    } else
      assert((size_t)val == i);
  }

  for (size_t i = 1; i < 50000; i++) {
    String* key = string_format("key %lu", i);
    hashmap_del(h, key);
  }
  assert(h->nitems == 0);

  for (size_t i = 1; i < 50000; i++) {
    String* key = string_format("key %lu", i);
    assert(hashmap_get(h, key) == NULL);
  }

  for (size_t i = 1; i < 50000; i++) {
    String* key = string_format("key %lu", i);
    hashmap_put(h, key, (void*)i);
    assert((size_t)hashmap_get(h, key) == i);
  }

  printf("hashmap test completed\n");
  return 0;
}
