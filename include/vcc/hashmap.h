#ifndef VCC_HASHMAP_H
#define VCC_HASHMAP_H

#include <stdbool.h>
#include <stdint.h>
#include <vcc/string.h>
#include <vcc/vec.h>

typedef struct {
  String* key;
  void* value;
  enum {
    INVALID = 0,
    VALID,
    TOMBSTONE,
  } state;
} HashmapEntry;

typedef struct {
  size_t nitems;
  size_t ntombstones;
  size_t cap;
  HashmapEntry* entries;
} Hashmap;

Hashmap* hashmap_new(void);

// Returns the value corresponding to the given key.
// Returns NULL if the key doesn't exist.
void* hashmap_get(Hashmap* h, String* key);

// Puts the (key, value) pair in the hashmap.
// If the key already exists, then it's updated in place.
void hashmap_put(Hashmap* h, String* key, void* value);

// Deletes the key from the hashmap.
// Does nothing if key isn't in the hashmap.
void hashmap_del(Hashmap* h, String* key);

#endif
