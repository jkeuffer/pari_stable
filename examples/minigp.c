#include <stdio.h>
#include <pari/pari.h>
#include <readline/readline.h>
#include <setjmp.h>

char * prompt = NULL;
jmp_buf env;

GEN sd_prompt(const char *v, long flag)
{
  if (v) { pari_free(prompt); prompt = strdup(v); }
  if (flag == d_RETURN) return strtoGENstr(prompt);
  else if (flag == d_ACKNOWLEDGE)
    pari_printf("   prompt = \"%s\"\n", prompt);
  return gnil;
}
void gp_err_recover(long numerr) { longjmp(env, numerr); }
void gp_quit(long exitcode) { exit(exitcode); }
void help(const char *s)
{ 
  entree *ep = is_entry(s);
  if (ep && ep->help)
    pari_printf("%s\n",ep->help);
  else 
    pari_printf("Function %s not found\n",s);
}

int main(int argc, char **argv)
{
  entree functions_gp[]={
    {"quit",0,(void*)gp_quit,11,"vD0,L,","quit({status = 0}): quit, return to the system with exit status 'status'."},
    {"help",0,(void*)help,11,"vr","help(fun): display help for function fun"},
    {NULL,0,NULL,0,NULL,NULL}};
  entree default_gp[]={
    {"prompt",0,(void*)sd_prompt,16,"","(default) string to be printed as prompt"},
    {NULL,0,NULL,0,NULL,NULL}};
  pari_init(8000000,500000);
  pari_add_module(functions_gp);
  pari_add_defaults_module(default_gp);
  sd_prompt("? ",d_INITRC);
  pari_printf("Welcome to minigp!\n");
  cb_pari_err_recover = gp_err_recover;
  (void)setjmp(env);
  while(1)
  {
    char *in = readline(prompt);
    GEN z;
    if (!in) break;
    if (!*in) continue;
    z = gp_read_str(in);
    if (z != gnil)
      pari_printf("%%%lu = %Ps\n",pari_nb_hist(),pari_add_hist(z));
    free(in); avma=top;
  }
  return 0;
}
