/*
 * proxy.c
 *
 * Derek Tzeng
 * dtzeng
 *
 * This proxy accepts incoming connections from clients, forwards the request
 * the server, and then forwards the response from the server back to the
 * client.
 *
 * Multiple concurrent connections are supported. The proxy will spawn a new
 * thread for each new connection with the Pthreads library.
 *
 * This proxy also maintains a cache that caches most recently added web
 * objects. The cache will be restricted to a maximum size, and each object
 * will also be restricted to a maximum size, so no object will
 * unproportionally consume the cache.  For more cache implementation
 * information, see "cache.c".
 *
 * To keep the cache thread-safe, the proxy uses the read/write locking
 * primitives that are included in the Pthreads library.
 *
 */

#include "csapp.h"
#include "open_clientfd_r.h"
#include "cache.h"

/* Recommended max cache and object sizes */
#define MAX_CACHE_SIZE 1049000
#define MAX_OBJECT_SIZE 102400

/* You won't lose style points for including these long lines in your code */
static const char *user_agent_hdr = "User-Agent: Mozilla/5.0 (X11; Linux x86_64; rv:10.0.3) Gecko/20120305 Firefox/10.0.3\r\n";
static const char *accept_hdr = "Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8\r\n";
static const char *accept_encoding_hdr = "Accept-Encoding: gzip, deflate\r\n";
static const char *connection_hdr = "Connection: close\r\n";
static const char *proxy_connection_hdr = "Proxy-Connection: close\r\n";

/* Global variables for caching and locking */
cache *proxy_cache;
pthread_rwlock_t rwlock;

/* Function declarations */
void *new_request(void *vargp);
void read_request(int fd, rio_t *rio, char *request, char *uri);
char *read_uri(char *uri, char *host, char *remain);
void cat_requesthdrs(rio_t *rio, char *req_headers);
void remove_newline(char *header);
void clienterror(int fd, char *cause, char *errnum,
		 char *shortmsg, char *longmsg);


int main(int argc, char **argv) {
  int port, listenfd, clientlen, *connfd;
  struct sockaddr_in clientaddr;
  pthread_t tid;

  /* Initialize cache and lock */
  proxy_cache = cache_init(MAX_CACHE_SIZE);
  pthread_rwlock_init(&rwlock, NULL);

  if(argc < 2) {
    fprintf(stderr, "usage: %s <port>\n", argv[0]);
    exit(1);
  }
  port = atoi(argv[1]);

  /* Ignore broken pipe signals */
  Signal(SIGPIPE, SIG_IGN);

  listenfd = Open_listenfd(port);
  while(1) {
    clientlen = sizeof(clientaddr);
    connfd = Malloc(sizeof(int));
    *connfd = Accept(listenfd, (SA *)&clientaddr, (socklen_t *)&clientlen);
    Pthread_create(&tid, NULL, new_request, connfd);
  }
  return 0;
}

/*
 * new_request: Spawns a new thread for an incoming request.
 */
void *new_request(void *vargp) {
  Pthread_detach(pthread_self());

  char buf[MAXLINE];
  char request[MAXLINE], uri[MAXLINE], host[MAXLINE], remain[MAXLINE];
  char req_port[MAXLINE], req_headers[MAXLINE];
  rio_t rio_toclient, rio_toserver;
  int connfd = *((int *)vargp);
  free(vargp);

  read_request(connfd, &rio_toclient, request, uri);
  strcpy(req_port, read_uri(uri, host, remain));
  strcpy(req_headers, "");
  cat_requesthdrs(&rio_toclient, req_headers);

  /* Check if request is in the cache */
  object *retrieve;
  int found = 0;
  pthread_rwlock_rdlock(&rwlock);
  retrieve = find_request(proxy_cache, request);
  if(retrieve != NULL)
    found = 1;
  pthread_rwlock_unlock(&rwlock);
  if(found) {
    pthread_rwlock_rdlock(&rwlock);
    rio_writen(connfd, retrieve->response, retrieve->size);
    pthread_rwlock_unlock(&rwlock);
    if(errno != EPIPE)
      close(connfd); //Close connfd if not prematurely closed
    return NULL;
  }

  /* Send request to server */
  int serverfd;
  remove_newline(host);
  if((serverfd = open_clientfd_r(host, req_port)) < 0) {
    clienterror(connfd, "GET", "404", "Not found",
                "Requested URL could not be found");
    close(connfd);
    return NULL;
  }
  Rio_readinitb(&rio_toserver, serverfd);
  sprintf(buf, "GET %s HTTP/1.0\r\n", remain);
  if((rio_writen(serverfd, buf, strlen(buf))) < 0) {
    if(errno != EPIPE)
      close(serverfd); //Close serverfd if not prematurely closed
    close(connfd);
    return NULL;
  }
  sprintf(buf, "%s\r\n", req_headers);
  if((rio_writen(serverfd, buf, strlen(buf))) < 0) {
    if(errno != EPIPE)
      close(serverfd); //Close serverfd if not prematurely closed
    close(connfd);
    return NULL;
  }

  /* Forward response to client */
  int rc;
  int flag = 1;
  int total_size = 0;
  char *response = Malloc(MAX_OBJECT_SIZE);
  memset(response, '\0', MAX_OBJECT_SIZE);
  while((rc = rio_readnb(&rio_toserver, buf, MAXLINE)) > 0) {
    if(flag) {
      if((total_size + rc) <= MAX_OBJECT_SIZE) {
        memcpy(response + total_size, buf, rc);
        total_size += rc;
      }
      else {
        flag = 0;
        free(response);
      }
    }
    if((rio_writen(connfd, buf, rc)) < 0) {
      if(errno != EPIPE)
        close(connfd); //Close connfd if not prematurely closed
      close(serverfd);
      return NULL;
    }
  }

  /* Add new object to cache if necessary */
  if(flag && (errno != ECONNRESET)) {
    char *new_req = Malloc(strlen(request) + 1);
    memcpy(new_req, request, strlen(request) + 1);
    char *new_resp = Malloc(total_size);
    memcpy(new_resp, response, total_size);
    free(response);
    object *new_obj = new_object(new_req, new_resp, total_size);
    pthread_rwlock_wrlock(&rwlock);
    cache_insert(proxy_cache, new_obj);
    pthread_rwlock_unlock(&rwlock);
  }

  if(errno != ECONNRESET)
    close(serverfd); //Close serverfd if not prematurely closed
  close(connfd);
  return NULL;
}

/*
 * read_request: Reads and parses the request line.
 */
void read_request(int fd, rio_t *rio, char *request, char *uri) {
  char buf[MAXLINE];
  char method[MAXLINE], version[MAXLINE];
  Rio_readinitb(rio, fd);
  if((rio_readlineb(rio, buf, MAXLINE)) < 0) {
    clienterror(fd, method, "400", "Bad Request",
                "Proxy could not be understood");
  }
  strcpy(request, buf);
  sscanf(buf, "%s %s %s", method, uri, version);
  if(strcasecmp(method, "GET")) {
    clienterror(fd, method, "501", "Not Implemented",
                "Proxy only supports GET method");
  }
  return;
}

/*
 * read_uri : Parses the URI into host and remain,
 *            and returns the requested port (default 80).
 */
char *read_uri(char *uri, char *host, char *remain) {
  char *uri_p = uri;
  char *req_port = "-1";

  /* Ignore "http://" */
  if(strncasecmp(uri, "http://", 7) == 0) {
    uri_p += 7;
  }

  /* Copy host */
  int i;
  for(i = 0; (*uri_p != '\0') && (*uri_p != '/'); i++) {
    /* Record requested port if necessary */
    if(*uri_p == ':') {
      char port_s[10] = "";
      char *port_p = uri_p + 1;
      int y;
      for(y = 0; (*port_p != '\0') && (*port_p != '/'); y++) {
        port_s[y] = *port_p;
        port_p++;
      }
      for(; y < 10; y++) {
        port_s[y] = '\0';
      }
      uri_p = port_p;
      req_port = port_s;
      break;
    }
    host[i] = *uri_p;
    uri_p++;
  }
  for(; i < MAXLINE; i++) {
    host[i] = '\0';
  }

  /* Copy remaining path */
  strcpy(remain, uri_p);

  if(atoi(req_port) < 0) {
    return "80";
  }
  return req_port;
}

/*
 * cat_requesthdrs: Reads the request headers and
 *                  appends them to req_headers.
 */
void cat_requesthdrs(rio_t *rio, char *req_headers) {
  char buf[MAXLINE];

  Rio_readlineb(rio, buf, MAXLINE);
  while(strcmp(buf, "\r\n")) {
    char h_key[MAXLINE], h_value[MAXLINE];
    sscanf(buf, "%[^:]: %s", h_key, h_value);

    /* Keep additional request headers */
    if(strcasecmp(h_key, "User-Agent") &&
       strcasecmp(h_key, "Accept") &&
       strcasecmp(h_key, "Accept-Encoding") &&
       strcasecmp(h_key, "Connection") &&
       strcasecmp(h_key, "Proxy-Connection")) {
      strcat(req_headers, buf);
    }
    Rio_readlineb(rio, buf, MAXLINE);
  }

  /* Concatenate remaining request headers */
  strcat(req_headers, user_agent_hdr);
  strcat(req_headers, accept_hdr);
  strcat(req_headers, accept_encoding_hdr);
  strcat(req_headers, connection_hdr);
  strcat(req_headers, proxy_connection_hdr);
}

/*
 * remove_newline: Removes the termination characters in a header value
 */
void remove_newline(char *header) {
  int x;
  char *header_p = header;
  for(x = 0; (*header_p != '\r') && (*header_p != '\0'); x++) {
    header_p++;
  }
  for(; x < MAXLINE; x++) {
    header[x] = '\0';
  }
}

/*
 * clienterror - returns an error message to the client
 */
void clienterror(int fd, char *cause, char *errnum,
		 char *shortmsg, char *longmsg) {
  char buf[MAXLINE], body[MAXBUF];

  /* Build the HTTP response body */
  sprintf(body, "<html><title>Tiny Error</title>");
  sprintf(body, "%s<body bgcolor=""ffffff"">\r\n", body);
  sprintf(body, "%s%s: %s\r\n", body, errnum, shortmsg);
  sprintf(body, "%s<p>%s: %s\r\n", body, longmsg, cause);
  sprintf(body, "%s<hr><em>The Tiny Web server</em>\r\n", body);

  /* Print the HTTP response */
  sprintf(buf, "HTTP/1.0 %s %s\r\n", errnum, shortmsg);
  if(rio_writen(fd, buf, strlen(buf)) < 0) {
    if(errno != EPIPE)
      close(fd);
  }
  sprintf(buf, "Content-type: text/html\r\n");
  if(rio_writen(fd, buf, strlen(buf)) < 0) {
    if(errno != EPIPE)
      close(fd);
  }
  sprintf(buf, "Content-length: %d\r\n\r\n", (int)strlen(body));
  if(rio_writen(fd, buf, strlen(buf)) < 0) {
    if(errno != EPIPE)
      close(fd);
  }
  if(rio_writen(fd, body, strlen(body)) < 0) {
    if(errno != EPIPE)
      close(fd);
  }
}
