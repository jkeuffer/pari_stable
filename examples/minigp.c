#include <stdio.h>
#include <pari/pari.h>
#include <readline/readline.h>
#include <setjmp.h>

jmp_buf env;
void gp_err_recover(long numerr) { longjmp(env, numerr); }

int main(int argc, char **argv)
{
  char *in;
  GEN z;
  pari_init(8000000,500000);
  pari_printf("Welcome to minigp!\n");
  cb_pari_err_recover = gp_err_recover;
  (void)setjmp(env);
  while(1)
  {
    in = readline("? ");
    if (!in) break;
    if (!*in) continue;
    z = pari_add_hist(gp_read_str(in));
    pari_printf("%%%lu = %Ps\n",pari_nb_hist(),z);
    free(in); avma=top;
  }
  return 0;
}
