#include "open_clientfd_r.h"

/*
 * open_clientfd_r - thread-safe version of open_clientfd
 */
int open_clientfd_r(char *hostname, char *port) {
    int clientfd;
    struct addrinfo *addlist, *p;
    int rv;

    /* Create the socket descriptor */
    if ((clientfd = socket(AF_INET, SOCK_STREAM, 0)) < 0) {
        return -1;
    }

    /* Get a list of addrinfo structs */
    if ((rv = getaddrinfo(hostname, port, NULL, &addlist)) != 0) {
        return -1;
    }

    /* Walk the list, using each addrinfo to try to connect */
    for (p = addlist; p; p = p->ai_next) {
        if ((p->ai_family == AF_INET)) {
            if (connect(clientfd, p->ai_addr, p->ai_addrlen) == 0) {
                break; /* success */
            }
        }
    }

    /* Clean up */
    freeaddrinfo(addlist);
    if (!p) { /* all connects failed */
        close(clientfd);
        return -1;
    }
    else { /* one of the connects succeeded */
        return clientfd;
    }
}

int Open_clientfd_r(char *hostname, char *port) {
  int rc;

  if((rc = open_clientfd_r(hostname, port)) < 0) {
    if(rc == -1)
      unix_error("Open_clientfd_r Unix error");
    else
      dns_error("Open_clientfd_r DNS error");
  }
  return rc;
}
