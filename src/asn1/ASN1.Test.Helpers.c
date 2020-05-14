#include <string.h>

_Bool buffer_eq (unsigned char *b1, unsigned char *b2, size_t l)
{
  return memcmp (b1, b2, l) == 0;
}
