squfof(n)=
{

  if (isprime(n), return(n));
  if (issquare(n), return(sqrtint(n)));

  p=factor(n,0)[1,1];
  if (p!=n, return(p));

  if (n%4==1,
    dd=n; d=sqrtint(dd); b=(((d-1)\2)<<1) + 1
  ,
    dd=n<<2; d=sqrtint(dd); b=(d\2)<<1
  );
  f=Qfb(1,b,(b^2-dd)>>2,0.);
  q=[]; lq=0; ii=0; l=sqrtint(d);

  while (1,
    f=qfbred(f,3,dd,d);
    ii++; a=component(f,1);
    if (!(ii%2),
      if (issquare(a),
	as=sqrtint(a); j=1;
	while (j<=lq,
	  if (as==q[j], break);
	  j++
	);
	if (j>lq, break)
      );
    );

    if (abs(a)<=l,
	q=concat(q,abs(a));
	print(q); lq++;
    )
  );

  gs=gcd(as,dd);
  print("i = ",ii); print(f);
  gs=gcd(gs,bb=component(f,2));
  if (gs>1, return (gs));

  g=qfbred(Qfb(as,-bb,as*component(f,3),0.),3,dd,d);
  b=component(g,2);
  until (b1==b,
    b1=b; g=qfbred(g,3,dd,d);
    b=component(g,2);
  );
  a=abs(component(g,1));
  if (!(a%2),a>>=1);
  a
}
