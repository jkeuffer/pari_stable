rgcd(a,b)=
{
  local(r);

  a=abs(a); b=abs(b);
  while(b > 0.01,
    r = a - b*truncate(a/b);
    a=b; b=r
  );
  a
}

f(a,b)=
{
  local(j,s,n,l,mv,vreg,cp);

  s=a+b*t; n=abs(norm(s));
  mv=vectorv(li);
  forprime(k=2,plim,
    l=0; while (!(n%k), l++; n/=k);
    if (l,
      j=ind[k];cp=v[j][2];
      while((a+b*cp)%k,
	j++; cp=v[j][2]
      );
      mv[j]=l
    )
  );
  if (n!=1, return);

  vreg=vectorv(lireg,j,
    if (j<=r1,
      log(abs(a+b*re[j]))
    ,
      log(norm(a+b*re[j]))
    )
  );
  mreg=concat(mreg,vreg); m=concat(m,mv);
  areg=concat(areg,a+b*t);
  print1("(" res++ ": " a "," b ")")
}

clareg(p, plim=19, lima=50, extra=5)=
{
  vi=nfinit(p); p=vi.pol;
  t=Mod(x,p,1);
  r=vi.roots; r1=vi.sign[1];
  findex=vi[4]; /* index: power basis <==> findex = 1 */
  if (findex>1,
    error("sorry, the case f>1 is not implemented")
  );

  print("discriminant = " vi.disc ", signature = " vi.sign);
  dep=length(p)-1;
  lireg=(dep+r1)/2;
  re=vector(lireg,j,
    if (j<=r1, real(r[j]) , r[j])
  );
  ind=vector(plim); v=[];
  forprime(k=2,plim,
    w=lift(factormod(p,k));
    find=0;
    for(l=1,length(w[,1]),
      fa=w[l,1];
      if (length(fa)==2,
	if (!find,
	  find=1; ind[k]=length(v)+1
	);
	v=concat(v,[[k,-polcoeff(fa,0),w[l,2]]])
      )
    )
  );
  li=length(v); co=li+extra;
  res=0; print("need " co);
  areg=[]~; mreg = m = [;];
  a=1; b=1; f(0,1);
  while (res<co,
    if (gcd(a,b)==1,
      f(a,b); f(-a,b)
    );
    a++;
    if (a*b>lima, b++; a=1)
  );
  print(" ");
  mh=mathnf(m); ms=matsize(mh);
  if (ms[1]!=ms[2],
    print("not enough relations for class group: matrix size = ",ms);
    return
  );

  mhs=matsnf(mh); clh=mhs[1]; mh1=[clh];
  j=1;
  while (j<length(mhs),
    j++;
    if (mhs[j]>1,
      mh1=concat(mh1,mhs[j]);
      clh *= mhs[j]
    )
  );
  print("class number = " clh ", class group = " mh1);
  areg=Mat(areg); km=matkerint(m); mregh=mreg*km;
  if (lireg==1,
    a1=1
  ,
    coreg=length(mregh);
    if (coreg<lireg-1,
      print("not enough relations for regulator: matsize = " matsize(mregh));
      a1 = "(not given)";
    ,
      mreg1=vecextract(mregh, Str(1 ".." lireg-1), "..");
      a1 = 0;
      for(j=lireg-1,coreg,
        a = matdet(vecextract(mreg1, Str(j-lireg+2 ".." j)));
	a1 = if (a1, a, rgcd(a1,a))
      );
    )
  );
  print("regulator = " a1)
}

check(lim=200) =
{
  r1=vi.sign[1]; r2=vi.sign[2]; pol=vi.pol;
  z = 2^(-r1) * (2*Pi)^(-r2) * sqrt(abs(vi.disc));
  forprime (q=2,lim,
    z *= (q-1)/q; fa=factormod(pol,q,1)[,1];
    z /= prod(i=1, length(fa), 1 - 1/q^fa[i])
  );
  clh*a1/nfrootsof1(vi)[1]/z
}

fu() = vector(length(km), k, factorback(concat(areg, km[,k])))
