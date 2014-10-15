#include "csapp.h"

typedef struct object object;
typedef struct cache cache;

struct object {
  char *request;
  char *response;
  int size;
  object *prev;
  object *next;
};

struct cache {
  int bytes_left;
  object *MRA;
  object *LRA;
};


cache *cache_init(int max_size);
void cache_free(cache *C);
void cache_insert(cache *C, object *obj);
void cache_remove(cache *C, object *obj);
object *new_object(char *req, char *resp, int obj_size);
void evict(cache *C, int req_size);
object *find_request(cache *C, char *req);
