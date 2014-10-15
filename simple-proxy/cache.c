/*
 * cache.c
 *
 * Derek Tzeng
 * dtzeng
 *
 *
 * This cache is meant to store web objects and approximates the LRU
 * eviction policy by evicting least recently added objects.
 *
 * The cache stores the objects in a doubly linked list, where the first
 * object is the most recently added (MRA) and the last object is the
 * least recently added (LRA). The cache also keeps track of how many bytes
 * are left for usage.
 *
 * An object keeps track of the request, the response of the request,
 * and the size of the object in bytes. The object also includes a previous
 * and next pointer for the doubly linked list implementation.
 *
 * To provide space for a new insertion, least recently added objects are
 * continually evicted until the required space is sufficient.
 *
 */

#include "cache.h"

/*
 * cache_init: Allocates a new cache and returns it.
 */
cache *cache_init(int max_size) {
  cache *C = Malloc(sizeof(cache));
  C->bytes_left = max_size;
  C->MRA = NULL;
  C->LRA = NULL;
  return C;
}

/*
 * cache_free: Frees the given cache.
 */
void cache_free(cache *C) {
  while(C->MRA != NULL) {
    cache_remove(C, C->MRA);
  }
  free(C);
}

/*
 * cache_insert: Evicts for sufficient space, then inserts the given object
 *               into the cache as the MRA object.
 */
void cache_insert(cache *C, object *obj) {
  evict(C, obj->size);
  C->bytes_left -= obj->size;

  if(C->MRA == NULL) {
    C->MRA = obj;
    C->LRA = obj;
  }
  else {
    object *temp = C->MRA;
    C->MRA = obj;
    obj->prev = NULL;
    obj->next = temp;
    temp->prev = obj;
  }
  return;
}

/*
 * cache_remove: Removes the given object from the cache.
 */
void cache_remove(cache *C, object *obj) {
  C->bytes_left += obj->size;
  if(obj->prev == NULL && obj->next == NULL) {
    C->MRA = NULL;
    C->LRA = NULL;
  }
  else if(obj->prev == NULL) {
    C->MRA = obj->next;
    C->MRA->prev = NULL;
  }
  else if(obj->next == NULL) {
    C->LRA = obj->prev;
    C->LRA->next = NULL;
  }
  else {
    object *prev_obj = obj->prev;
    object *next_obj = obj->next;
    prev_obj->next = next_obj;
    next_obj->prev = prev_obj;
  }

  free(obj->request);
  free(obj->response);
  free(obj);
  return;
}

/*
 * new_object: Allocates a new object and returns it.
 */
object *new_object(char *req, char *resp, int obj_size) {
  object *obj = Malloc(sizeof(object));
  obj->request = req;
  obj->response = resp;
  obj->size = obj_size;
  obj->prev = NULL;
  obj->next = NULL;
  return obj;
}

/*
 * evict: Evicts LRA objects from the cache until the cache has enough space
 *        for the requested size.
 */
void evict(cache *C, int req_size) {
  while(C->bytes_left < req_size) {
    cache_remove(C, C->LRA);
  }
}

/*
 * find_request: Finds the request in the cache and returns the object.
 *               If the request was not found, returns NULL.
 */
object *find_request(cache *C, char *req) {
  object *scan;
  for(scan = C->MRA; scan != NULL; scan = scan->next) {
    if((strcmp(req, scan->request)) == 0) {
      return scan;
    }
  }
  return NULL;
}
