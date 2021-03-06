/*
*      get-tree.c - receive an MP tree from a single master (put-tree).
*
*/

#include <stdio.h>

#include <sys/types.h>
#include <fcntl.h>
#include <stdio.h>
#include <math.h>
#include "pvm3.h"
#include "MP.h"

EXTERN MP_TranspOps_t pvm_ops;

FILE         *fd;

#include "node.c"

int 
process_request(root, lfd)
  node_t *root;
  FILE *lfd;
{
  int more;

  more = print_node(root, lfd);
  return more;
}

main(argc, argv)
  int argc;
  char *argv[];
{
  int mytid;                  /* my task id */
  int stid = 0;		      /* slave task id */
  int n, i, more = 0;
  int spawn_flag = PvmTaskDefault;
  char filename[128], *ofile = NULL;
  MP_Env_pt  env  = NULL;
  MP_Link_pt link = NULL; 
  node_t    *root = NULL;

  pvm_setopt(PvmAutoErr, 0); /* tell PVM not to print error to stdout */
  if ((mytid = pvm_mytid()) < 0) {
		exit(1);
  }

  ofile = IMP_GetCmdlineArg(argc, argv, "-outfile");
  if (ofile == NULL) ofile = "/tmp/get-tree.out";
  fd = fopen(ofile, "w");

  env = MP_AllocateEnv();
  MP_SetEnvOption(env, MP_BUFFER_SIZE_OPT, pvm_getopt(PvmFragSize));
  if ((env = MP_InitializeEnv(env)) == NULL) {
    fprintf(stderr, "%s: MP_EnvInitialize() failed!\n", argv[0]);
    exit(1);
  }
  MP_AddEnvTranspDevice(env, MP_PvmTransportDev, &pvm_ops);

  if ((link = MP_OpenLink(env, argc, argv)) == NULL) {
    fprintf(stderr, "%s: MP_OpenLink() failed!\n", argv[0]);
    exit(1);
    }
  
  MP_SetLinkOption(link, MP_LINK_LOG_MASK_OPT, MP_LOG_INIT_EVENTS);
  MP_SetLinkOption(link, MP_LINK_LOG_MASK_OPT, MP_LOG_READ_EVENTS);
  MP_SetLinkOption(link, MP_LINK_LOG_MASK_OPT, MP_LOG_WRITE_EVENTS);

  pvm_initsend(PvmDataDefault);
  stid = pvm_parent();
  pvm_send(stid, 0 );  /* let the parent know I am ready */

  printf("server's annotated tree(s):\n");
  do {
    if (MP_TestEofMsg(link))  MP_SkipMsg(link);
    printf("\n\ntype\t\t  #annots      value\t#children\n");
    /* STEP 1: get the request */
       root = m_get_node(link);
    /* STEP 2: process the request */
       more = process_request(root, fd); 

    /* STEP 3: cleanup */
       free_tree(root);     /* free the annotated tree */
       root = NULL; 
       free_label_table();  /* free the label table    */
  } while (more);

  fflush(fd); fclose(fd);
  MP_CloseLink(link);
  MP_ReleaseEnv(env);
  printf("\nget-tree: Successful termination.\n");
  pvm_exit();
  exit(0);

bail: 
  if (stid > 0)
    pvm_kill(stid);
  pvm_exit();
  exit(1);
}


