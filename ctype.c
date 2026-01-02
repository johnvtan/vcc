#include <assert.h>
#include <stdlib.h>
#include <vcc/ctype.h>

bool c_type_eq(CType* c1, CType* c2) { return c1->ty == c2->ty; }

CType* basic_data_type(CTypeKind ty) {
  CType* ret = calloc(1, sizeof(CType));
  ret->ty = ty;
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
