#include "csapp.h"

/* Thread safe open_clientfd */
int open_clientfd_r(char *hostname, char *port);

/* Wrapper for thread safe open_clientfd */
int Open_clientfd_r(char *hostname, char *port);
