main()
{
  if (sizeof(long) == 4)
  {
    union { double f; unsigned long i[2] } fi;
    fi.f = 2.;
    if (fi.i[0]==0 && fi.i[1]==(1UL<<30)) printf("1234\n");
    else if (fi.i[1]==0 && fi.i[0]==(1UL<<30)) printf("4321\n");
    else
      printf("UNKNOWN\n");
  }
  else
  {
    union { double f; unsigned long i } fi;
    fi.f = 2.;
    if (fi.i==(1UL<<62)) printf("12345678\n");
    else
      printf("UNKNOWN\n");
  }
  exit(0);
}
