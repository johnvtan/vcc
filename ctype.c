#include <assert.h>
#include <stdlib.h>
#include <vcc/ctype.h>

bool c_type_eq(const CType* c1, const CType* c2) {
  if (c1->ty != c2->ty) {
    return false;
  }

  if (c1->ty == CTYPE_FN) {
    if (!c_type_eq(c1->fn.return_type, c2->fn.return_type)) {
      return false;
    }

    if (c1->fn.param_types->len != c2->fn.param_types->len) {
      return false;
    }

    // Check all params
    for (size_t i = 0; i < c1->fn.param_types->len; i++) {
      CType* p1 = vec_get(c1->fn.param_types, i);
      CType* p2 = vec_get(c2->fn.param_types, i);
      if (!c_type_eq(p1, p2)) {
        return false;
      }
    }
  }

  if (c1->ty == CTYPE_PTR) {
    assert(false);  // TODO
  }

  return true;
}

static CType* new_c_type(CTypeKind ty) {
  CType* ret = calloc(1, sizeof(CType));
  ret->ty = ty;
  return ret;
}

CType* basic_data_type(CTypeKind ty) {
  assert(ty != CTYPE_FN);
  return new_c_type(ty);
}

CType* function_type(CType* return_type, Vec* param_types) {
  CType* ret = new_c_type(CTYPE_FN);
  ret->fn.return_type = return_type;
  ret->fn.param_types = param_types;
  return ret;
}

CType* pointer_to(CType* base) {
  CType* ret = new_c_type(CTYPE_PTR);
  ret->ptr_ref = base;
  return ret;
}

TypeSize get_type_size(CType* ty) {
  switch (ty->ty) {
    case CTYPE_INT:
    case CTYPE_UINT:
      return SIZE_INT;
    case CTYPE_LONG:
    case CTYPE_ULONG:
      return SIZE_LONG;
    default:
      assert(false);
  }
}

bool is_signed(CType* ty) {
  switch (ty->ty) {
    case CTYPE_INT:
    case CTYPE_LONG:
      return true;
    default:
      return false;
  }
}

bool is_integer(CType* ty) {
  switch (ty->ty) {
    case CTYPE_INT:
    case CTYPE_UINT:
    case CTYPE_LONG:
    case CTYPE_ULONG:
      return true;
    case CTYPE_DOUBLE:
    default:
      return false;
  }
}

bool is_float(CType* ty) { return ty->ty == CTYPE_DOUBLE; }

CType* get_common_type(CType* t1, CType* t2) {
  if (c_type_eq(t1, t2)) {
    return t1;
  }

  if (t1->ty == CTYPE_DOUBLE || t2->ty == CTYPE_DOUBLE) {
    return basic_data_type(CTYPE_DOUBLE);
  }

  TypeSize t1_size = get_type_size(t1);
  TypeSize t2_size = get_type_size(t2);

  if (t1_size == t2_size) {
    if (is_signed(t1)) {
      return t2;
    }
    return t1;
  }

  return t1_size > t2_size ? t1 : t2;
}
