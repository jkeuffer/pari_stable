main()
{
  int i;
  union
  {
    unsigned long l;
    char c[sizeof(long)];
  } u;

  if (sizeof(long) > 4) /* avoid "left shift count >= width of type" warning */
    u.l = (0x80706050UL << 28) | 0x04030201UL;
  else
    u.l = 0x04030201UL;
  for (i = 0; i < sizeof(long); i++)
    printf("%c", u.c[i]+'0');
  printf("\n");
  exit(0);
}

