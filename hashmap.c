#include <assert.h>
#include <stdlib.h>
#include <vcc/hashmap.h>

#define HASHMAP_INIT_CAP (16U)
#define HASHMAP_MAX_USAGE_PCT (70U)

static inline bool valid(Hashmap* h) {
  return h && h->entries && (h->nitems + h->ntombstones < h->cap);
}

static uint64_t fnv_hash(const String* key) {
  uint64_t hash = 0xcbf29ce484222325;
  for (size_t i = 0; i < string_len(key); i++) {
    hash *= 0x100000001b3;
    hash ^= string_get(key, i);
  }
  return hash;
}

// Usage pct of the hashmap is the ratio of (items + tombstones)
// over the total capacity.
// Tombstones are counted as part of usage so that we still rehash
// even if we don't have many items in the hashmap, but have a lot
// of tombstones.
static inline size_t usage_pct(const Hashmap* h) {
  return ((h->nitems + h->ntombstones) * 100) / h->cap;
}

// Return the entry containing key or a different entry that will
// be used to insert a new value. This function assumes that the
// caller intends to update the value corresponding to the key.
static HashmapEntry* get_or_insert(Hashmap* h, const String* key) {
  size_t hash = fnv_hash(key);
  HashmapEntry* tombstone = NULL;

  for (size_t i = 0; i < h->cap; i++) {
    size_t idx = (hash + i) % h->cap;
    HashmapEntry* e = &h->entries[idx];

    if (e->state == INVALID) {
      // if we get to an invalid slot, we return
      // the a tombstone slot if we found one,
      // or this slot if not.
      return tombstone ? tombstone : e;
    }

    if (e->state == TOMBSTONE && !tombstone) {
      // we'll return the first tombstoned slot,
      // but we need to keep searching until we reach
      // an invalid slot or a slot containing the
      // given key.
      tombstone = e;
      continue;
    }

    if (e->state == VALID && string_eq(e->key, key)) {
      // if we find the slot with the given key, we either
      // return the earlier tombstone slot to make searches
      // quicker later. we assume that the caller intends
      // to update the value anyway.
      // We need to then mark the slot with the key as a
      // tombstone.
      if (tombstone) {
        e->key = NULL;
        e->state = TOMBSTONE;
        e->value = NULL;
        return tombstone;
      }

      // no tombstone found -- just return the slot with
      // the key.
      return e;
    }
  }

  // unreachable
  assert(false);
}

// Returns the entry containing key or NULL if key isn't in
// the hashmap.
static HashmapEntry* get(Hashmap* h, const String* key) {
  size_t hash = fnv_hash(key);
  for (size_t i = 0; i < h->cap; i++) {
    size_t idx = (hash + i) % h->cap;
    HashmapEntry* e = &h->entries[idx];

    if (e->state == VALID && string_eq(key, e->key)) return e;

    if (e->state == INVALID) return NULL;

    // keep searching on TOMBSTONE
  }

  // unreachable
  assert(false);
}

// Reallocates the entries and re-inserts all the entries.
// This also resets the number of tombstones to 0 and may double
// the capacity.
// TODO the sizing could be better. Instead of always doubling
// capacity we sometimes want to shrink the hashmap if we have
// a large number of tombstones.
static void rehash(Hashmap* h) {
  HashmapEntry* old_entries = h->entries;
  size_t old_cap = h->cap;

  // recalculate usage after setting ntombstones to 0
  // to see if we actually need to grow the map
  h->ntombstones = 0;
  if (usage_pct(h) >= HASHMAP_MAX_USAGE_PCT) h->cap *= 2;

  h->entries = calloc(h->cap, sizeof(HashmapEntry));

  size_t count = 0;
  for (size_t i = 0; i < old_cap; i++) {
    HashmapEntry* old = &old_entries[i];

    // only VALID entries are reinserted
    if (old->state != VALID) continue;

    count++;
    HashmapEntry* new = get_or_insert(h, old->key);
    assert(new && old && old->state == VALID);

    new->key = old->key;
    new->state = VALID;
    new->value = old->value;
  }

  // sanity check number of items
  assert(count == h->nitems);
}

Hashmap* hashmap_new(void) {
  Hashmap* ret = calloc(1, sizeof(Hashmap));
  assert(ret);

  ret->cap = HASHMAP_INIT_CAP;
  ret->nitems = 0;
  ret->entries = calloc(ret->cap, sizeof(HashmapEntry));

  assert(valid(ret));
  return ret;
}

void* hashmap_get(Hashmap* h, String* key) {
  assert(valid(h) && key);
  HashmapEntry* e = get(h, key);
  assert(!e || e->state == VALID);
  return e ? e->value : NULL;
}

void hashmap_put(Hashmap* h, String* key, void* value) {
  assert(valid(h) && key && value);

  if (usage_pct(h) >= HASHMAP_MAX_USAGE_PCT) rehash(h);

  HashmapEntry* e = get_or_insert(h, key);
  assert(e);
  assert((e->state == VALID && string_eq(key, e->key)) ||
         e->state == TOMBSTONE || e->state == INVALID);

  e->key = key;
  e->state = VALID;
  e->value = value;
  h->nitems++;
}

void hashmap_del(Hashmap* h, String* key) {
  assert(valid(h) && key);
  HashmapEntry* e = get(h, key);
  if (e) {
    assert(e->state == VALID);
    e->state = TOMBSTONE;
    h->nitems--;
    h->ntombstones++;
  }
}
