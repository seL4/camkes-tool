/*
 * Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <camkes/error.h>

#define ERR_IF_BUFFER_LENGTH_EXCEEDED(size, curr_offset, desired, method,      \
                                      param)                                   \
  ERR_IF((desired) > ((size) - (curr_offset)), CAMKES_ERROR_HANDLER,           \
         ((camkes_error_t){                                                    \
             .type = CE_BUFFER_LENGTH_EXCEEDED,                                \
             .instance = CAMKES_INSTANCE_NAME,                                 \
             .interface = CAMKES_INTERFACE_NAME,                               \
             .description =                                                    \
                 "buffer exceeded while marshalling " param " in " method,     \
             .current_length = curr_offset,                                    \
             .target_length = curr_offset + desired,                           \
         }),                                                                   \
         ({ return UINT_MAX; }));

#define ERR_IF_MALFORMED_RPC_PAYLOAD(size, curr_offset, desired, method,       \
                                     param, cleanup_action)                    \
  ERR_IF((desired) > ((size) - (curr_offset)), CAMKES_ERROR_HANDLER,           \
         ((camkes_error_t){                                                    \
             .type = CE_MALFORMED_RPC_PAYLOAD,                                 \
             .instance = CAMKES_INSTANCE_NAME,                                 \
             .interface = CAMKES_INTERFACE_NAME,                               \
             .description =                                                    \
                 "truncated message encountered while unmarshalling " param    \
                 " for " method,                                               \
             .length = (size),                                                 \
             .current_index = (curr_offset) + (desired),                       \
         }),                                                                   \
         ({ cleanup_action; }));

#define ERR_IF_MALFORMED_RPC_EXCESS_PAYLOAD(size, received_length, method,     \
                                            cleanup_action)                    \
  ERR_IF(ROUND_UP_UNSAFE((received_length), sizeof(seL4_Word)) != (size),      \
         CAMKES_ERROR_HANDLER,                                                 \
         ((camkes_error_t){                                                    \
             .type = CE_MALFORMED_RPC_PAYLOAD,                                 \
             .instance = CAMKES_INSTANCE_NAME,                                 \
             .interface = CAMKES_INTERFACE_NAME,                               \
             .description = "excess trailing bytes after unmarshalling "       \
                            "parameters for " method,                          \
             .length = (size),                                                 \
             .current_index = (received_length),                               \
         }),                                                                   \
         ({ cleanup_action; }));

#define ERR_IF_ALLOCATION_FAILURE(result, size, method, param, cleanup_action) \
  ERR_IF((result) == NULL, CAMKES_ERROR_HANDLER,                               \
         ((camkes_error_t){                                                    \
             .type = CE_ALLOCATION_FAILURE,                                    \
             .instance = CAMKES_INSTANCE_NAME,                                 \
             .interface = CAMKES_INTERFACE_NAME,                               \
             .description =                                                    \
                 "out of memory while unmarshalling " param " for " method,    \
             .alloc_bytes = (size),                                            \
         }),                                                                   \
         ({ cleanup_action; }));

#define MARSHAL_ARRAY_PARAM(ptr, ptr_sz, buffer, size, length, method_name,    \
                            param_name)                                        \
  ({                                                                           \
    ERR_IF_BUFFER_LENGTH_EXCEEDED(size, length, sizeof(*ptr_sz), method_name,  \
                                  param_name);                                 \
    memcpy(buffer + length, ptr_sz, sizeof(*ptr_sz));                          \
    length += sizeof(*ptr_sz);                                                 \
    ERR_IF_BUFFER_LENGTH_EXCEEDED(size, length, (sizeof(ptr[0]) * (*ptr_sz)),  \
                                  method_name, param_name);                    \
    memcpy(buffer + length, ptr, (sizeof(ptr[0]) * (*ptr_sz)));                \
    length + (sizeof(ptr[0]) * (*ptr_sz));                                     \
  })

#define MARSHAL_STRING_ARRAY_PARAM(ptr, ptr_sz, buffer, size, length,          \
                                   method_name, param_name)                    \
  ({                                                                           \
    ERR_IF_BUFFER_LENGTH_EXCEEDED(size, length, sizeof(*ptr_sz), method_name,  \
                                  param_name);                                 \
    memcpy(buffer + length, ptr_sz, sizeof(*ptr_sz));                          \
    length += sizeof(*ptr_sz);                                                 \
    for (int __i = 0; __i < *ptr_sz; __i++) {                                  \
      size_t __strlen = strnlen(ptr[__i], size - length);                      \
      ERR_IF_BUFFER_LENGTH_EXCEEDED(size, length, (__strlen + 1), method_name, \
                                    param_name)                                \
      /* If we didn't trigger an error, we now know this strcpy is safe. */    \
      (void)strcpy(buffer + length, ptr[__i]);                                 \
      length += (__strlen + 1);                                                \
    }                                                                          \
    length;                                                                    \
  })

#define MARSHAL_STRING_PARAM(ptr, buffer, size, length, method_name,           \
                             param_name)                                       \
  ({                                                                           \
    size_t __strlen = strnlen(ptr, size - length);                             \
    ERR_IF_BUFFER_LENGTH_EXCEEDED(size, length, (__strlen + 1), method_name,   \
                                  param_name);                                 \
    /* If we didn't trigger an error, we now know this strcpy is safe. */      \
    (void)strcpy(buffer + length, ptr);                                        \
    length + (__strlen + 1);                                                   \
  })

#define MARSHAL_PARAM(ptr, buffer, size, length, method_name, param_name)      \
  ({                                                                           \
    ERR_IF_BUFFER_LENGTH_EXCEEDED(size, length, sizeof(*ptr), method_name,     \
                                  param_name)                                  \
    memcpy(buffer + length, ptr, sizeof(*ptr));                                \
    length + sizeof(*ptr);                                                     \
  })

#define UNMARSHAL_ARRAY_PARAM(ptr, ptr_sz, buffer, size, length, method_name,  \
                              param_name, cleanup_action)                      \
  ({                                                                           \
    ERR_IF_MALFORMED_RPC_PAYLOAD(size, length, sizeof(*ptr_sz), method_name,   \
                                 param_name, cleanup_action);                  \
    memcpy(ptr_sz, buffer + length, sizeof(*ptr_sz));                          \
    length += sizeof(*ptr_sz);                                                 \
    *ptr = malloc(sizeof((*ptr)[0]) * (*ptr_sz));                              \
    ERR_IF_ALLOCATION_FAILURE(*ptr, sizeof((*ptr)[0]) * (*ptr_sz),             \
                              method_name, param_name, cleanup_action);        \
    ERR_IF_MALFORMED_RPC_PAYLOAD(size, length,                                 \
                                 (sizeof((*ptr)[0]) * (*ptr_sz)), method_name, \
                                 param_name, ({                                \
                                   free(*ptr);                                 \
                                   cleanup_action;                             \
                                 }));                                          \
    memcpy((*ptr), buffer + length, sizeof((*ptr)[0]) * (*ptr_sz));            \
    length + sizeof((*ptr)[0]) * (*ptr_sz);                                    \
  })

#define UNMARSHAL_STRING_ARRAY_PARAM(ptr, ptr_sz, buffer, size, length,        \
                                     method_name, param_name, cleanup_action)  \
  ({                                                                           \
    ERR_IF_MALFORMED_RPC_PAYLOAD(size, length, sizeof(*ptr_sz), method_name,   \
                                 param_name, cleanup_action);                  \
    memcpy(ptr_sz, buffer + length, sizeof(*ptr_sz));                          \
    length += sizeof(*ptr_sz);                                                 \
    *ptr = malloc(sizeof(char *) * (*ptr_sz));                                 \
    ERR_IF_ALLOCATION_FAILURE(*ptr, sizeof(char *) * (*ptr_sz), method_name,   \
                              param_name, cleanup_action);                     \
    for (int __i = 0; __i < *ptr_sz; __i++) {                                  \
      size_t __strlen = strnlen(buffer + length, size - length);               \
      ERR_IF_MALFORMED_RPC_PAYLOAD(size, length, (__strlen + 1), method_name,  \
                                   param_name, ({                              \
                                     for (int __j = 0; __j < __i; __j++) {     \
                                       free((*ptr)[__j]);                      \
                                     }                                         \
                                     free(*ptr);                               \
                                     cleanup_action;                           \
                                   }));                                        \
      /* If we didn't trigger an error, we now know this strdup is safe. */    \
      (*ptr)[__i] = strdup(buffer + length);                                   \
      ERR_IF_ALLOCATION_FAILURE((*ptr)[__i], __strlen + 1, method_name,        \
                                param_name, ({                                 \
                                  for (int __j = 0; __j < __i; __j++) {        \
                                    free((*ptr)[__j]);                         \
                                  }                                            \
                                  free(*ptr);                                  \
                                  cleanup_action;                              \
                                }));                                           \
      length += __strlen + 1;                                                  \
    }                                                                          \
    length;                                                                    \
  })

#define UNMARSHAL_STRING_PARAM(ptr, buffer, size, length, method_name,         \
                               param_name, cleanup_action)                     \
  ({                                                                           \
    size_t __strlen = strnlen(buffer + length, size - length);                 \
    ERR_IF_MALFORMED_RPC_PAYLOAD(size, length, (__strlen + 1), method_name,    \
                                 param_name, cleanup_action);                  \
    *ptr = strdup(buffer + length);                                            \
    ERR_IF_ALLOCATION_FAILURE(*ptr, __strlen + 1, method_name, param_name,     \
                              cleanup_action);                                 \
    length + __strlen + 1;                                                     \
  })

#define UNMARSHAL_PARAM(ptr, buffer, size, length, method_name, param_name,    \
                        cleanup_action)                                        \
  ({                                                                           \
    ERR_IF_MALFORMED_RPC_PAYLOAD(size, length, sizeof(*ptr), method_name,      \
                                 param_name, cleanup_action);                  \
    memcpy(ptr, buffer + length, sizeof(*ptr));                                \
    length + sizeof(*ptr);                                                     \
  })
