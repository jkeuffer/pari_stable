main()
{
  int i;
  union
  {
    unsigned long l;
    char c[sizeof(long)];
  } u;

  if (sizeof(long) > 4)
    u.l = (0x08070605L << 32) | 0x04030201L;
  else
    u.l = 0x04030201L;
  for (i = 0; i < sizeof(long); i++)
    printf("%c", u.c[i]+'0');
  printf("\n");
  exit(0);
}

