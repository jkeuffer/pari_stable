#include <pari.h>

/********************************************************************/
/**                                                                **/
/**                          MEMBER FUNCTIONS                      **/
/**                                                                **/
/********************************************************************/
#define is_ell(x) (typ(x) == t_VEC && lg(x)>=14)
#define is_bigell(x) (typ(x) == t_VEC && lg(x)>=20)
extern void member_err(char *s);
  
GEN
member_e(GEN x)
{
  x = get_primeid(x);
  if (!x) member_err("e");
  return (GEN)x[3];
}

GEN
member_f(GEN x)
{
  x = get_primeid(x);
  if (!x) member_err("f");
  return (GEN)x[4];
}

GEN
member_p(GEN x)
{
  int t; (void)get_nf(x,&t);
  if (t == typ_GAL)
    return gmael(x,2,1);
  x = get_primeid(x);
  if (!x) member_err("p");
  return (GEN)x[1];
}

GEN
member_bnf(GEN x)
{
  int t; x = get_bnf(x,&t);
  if (!x) member_err("bnf");
  return x;
}

GEN
member_nf(GEN x)
{
  int t; x = get_nf(x,&t);
  if (!x) member_err("nf");
  return x;
}

/* integral basis */
GEN
member_zk(GEN x)
{
  int t; GEN y = get_nf(x,&t);
  if (!y)
  {
    switch(t)
    {
      case typ_CLA: return gmael(x,1,4);
      case typ_Q: y = cgetg(3,t_VEC);
        y[1]=un; y[2]=lpolx[varn(x[1])]; return y;
    }
    member_err("zk");
  }
  return (GEN)y[7];
}

GEN
member_disc(GEN x) /* discriminant */
{
  int t; GEN y = get_nf(x,&t);
  if (!y)
  {
    switch(t)
    {
      case typ_Q  : return discsr((GEN)x[1]);
      case typ_CLA:
        x = gmael(x,1,3);
        if (typ(x) != t_VEC || lg(x) != 3) break;
        return (GEN)x[1];
      case typ_ELL: return (GEN)x[12];
    }
    member_err("disc");
  }
  return (GEN)y[3];
}

GEN
member_pol(GEN x) /* polynomial */
{
  int t; GEN y = get_nf(x,&t);
  if (!y)
  {
    switch(t)
    {
      case typ_CLA: return gmael(x,1,1);
      case typ_POL: return x;
      case typ_Q  : return (GEN)x[1];
      case typ_GAL: return (GEN)x[1];
    }
    if (typ(x)==t_POLMOD) return (GEN)x[2];
    if (typ(x)==t_VEC && lg(x) == 13) return gmael(x,11,1);
    member_err("pol");
  }
  return (GEN)y[1];
}

GEN
member_mod(GEN x) /* modulus */
{
  int t; (void)get_nf(x,&t);
  if (t == typ_GAL)
    return gmael(x,2,3);
  switch(typ(x))
  {
    case t_INTMOD: case t_POLMOD: case t_QUAD: break;
    default: member_err("mod");
  }
  return (GEN)x[1];
}

GEN
member_sign(GEN x) /* signature */
{
  int t; GEN y = get_nf(x,&t);
  if (!y)
  {
    if (t == typ_CLA) return gmael(x,1,2);
    member_err("sign");
  }
  return (GEN)y[2];
}

/* x assumed to be output by get_nf: ie a t_VEC with length 11 */
static GEN
nfmats(GEN x)
{
  GEN y;
  if (!x) return NULL;
  y = (GEN)x[5];
  if (typ(y) == t_VEC && lg(y) != 8) return NULL;
  return y;
}

GEN
member_t2(GEN x) /* T2 matrix */
{
  int t; x = nfmats(get_nf(x,&t));
  if (!x) member_err("t2");
  return gram_matrix((GEN)x[2]);
}

GEN
member_diff(GEN x) /* different */
{
  int t; x = nfmats(get_nf(x,&t));
  if (!x) member_err("diff");
  return (GEN)x[5];
}

GEN
member_codiff(GEN x) /* codifferent */
{
  int t; GEN y = nfmats(get_nf(x,&t));
  if (!y) member_err("codiff");
  return gdiv((GEN)y[6], absi((GEN)x[3]));
}

GEN
member_roots(GEN x) /* roots */
{
  int t; GEN y = get_nf(x,&t);
  if (!y)
  {
    if (t == typ_ELL && is_bigell(x)) return (GEN)x[14];
    if (t == typ_GAL) return (GEN)x[3];
    member_err("roots");
  }
  return (GEN)y[6];
}

/* assume x output by get_bnf: ie a t_VEC with length 10 */
static GEN
check_RES(GEN x, char *s)
{
  GEN y = (GEN)x[8];
  if (typ(y) != t_VEC || lg(y) < 4)
    member_err(s);
  return y;
}

GEN
member_clgp(GEN x) /* class group (3-component row vector) */
{
  int t; GEN y = get_bnf(x,&t);
  if (!y)
  {
    switch(t)
    {
      case typ_QUA:
        y = cgetg(4,t_VEC);
        for(t=1; t<4; t++) y[t] = x[t];
        return y;
      case typ_CLA: return gmael(x,1,5);
    }
    if (typ(x)==t_VEC)
      switch(lg(x))
      {
        case 3: /* no gen */
        case 4: return x;
      }
    member_err("clgp");
  }
  if (t==typ_BNR) return (GEN)x[5];
  y = check_RES(y, "clgp");
  return (GEN)y[1];
}

GEN
member_reg(GEN x) /* regulator */
{
  int t; GEN y = get_bnf(x,&t);
  if (!y)
  {
    switch(t)
    {
      case typ_CLA: return gmael(x,1,6);
      case typ_QUA: return (GEN)x[4];
    }
    member_err("reg");
  }
  if (t == typ_BNR) err(impl,"ray regulator");
  y = check_RES(y, "reg");
  return (GEN)y[2];
}

GEN
member_fu(GEN x) /* fundamental units */
{
  int t; GEN y = get_bnf(x,&t);
  if (!y)
  {
    switch(t)
    {
      case typ_CLA: x = (GEN)x[1]; if (lg(x) < 10) break;
        return (GEN)x[9];
      case typ_Q:
        x = discsr((GEN)x[1]);
        return (signe(x)<0)? cgetg(1,t_VEC): fundunit(x);
    }
    member_err("fu");
  }
  if (t == typ_BNR) err(impl,"ray units");
  return check_units(y,".fu");
}

/* torsion units. return [w,e] where w is the number of roots of 1, and e a
 * polymod generator */
GEN
member_tu(GEN x)
{
  int t; GEN y = get_bnf(x,&t), res = cgetg(3,t_VEC);
  if (!y)
  {
    switch(t)
    {
      case typ_Q:
        y = discsr((GEN)x[1]);
        if (signe(y)<0 && cmpis(y,-4)>=0)
          y = stoi((itos(y) == -4)? 4: 6);
        else
        { y = gdeux; x=negi(gun); }
        res[1] = (long)y;
        res[2] = (long)x; return res;
      case typ_CLA:
        x = (GEN)x[1];
        if (lg(x) > 8)
        {
          y = (GEN)x[8];
          if (typ(y) == t_VEC || lg(y) == 3) break;
        }
      default: member_err("tu");
    }
  }
  else
  {
    if (t == typ_BNR) err(impl,"ray torsion units");
    x = (GEN)y[7]; y=(GEN)y[8];
    if (typ(y) == t_VEC && lg(y) > 5) y = (GEN)y[4];
    else
    {
      y = rootsof1(x);
      y[2] = lmul((GEN)x[7], (GEN)y[2]);
    }
  }
  res[2] = y[2];
  res[1] = y[1]; return res;
}

GEN
member_futu(GEN x) /*  concatenation of fu and tu, w is lost */
{
  GEN fuc = member_fu(x);
  return concatsp(fuc, (GEN)member_tu(x)[2]);
}

GEN
member_tufu(GEN x) /*  concatenation of tu and fu, w is lost */
{
  GEN fuc = member_fu(x);
  return concatsp((GEN)member_tu(x)[2], fuc);
}

GEN
member_zkst(GEN bid)
/* structure of (Z_K/m)^*, where bid is an idealstarinit (with or without gen)
   or a bnrinit (with or without gen) */
{
  if (typ(bid)==t_VEC)
    switch(lg(bid))
    {
      case 6: return (GEN) bid[2];   /* idealstarinit */
      case 7: bid = (GEN)bid[2]; /* bnrinit */
        if (typ(bid) == t_VEC && lg(bid) > 2)
          return (GEN)bid[2];
    }
  member_err("zkst");
  return NULL; /* not reached */
}

GEN
member_no(GEN clg) /* number of elements of a group (of type clgp) */
{
  clg = member_clgp(clg);
  if (typ(clg)!=t_VEC  || (lg(clg)!=3 && lg(clg)!=4))
    member_err("no");
  return (GEN) clg[1];
}

GEN
member_cyc(GEN clg) /* cyclic decomposition (SNF) of a group (of type clgp) */
{
  clg = member_clgp(clg);
  if (typ(clg)!=t_VEC  || (lg(clg)!=3 && lg(clg)!=4))
    member_err("cyc");
  return (GEN) clg[2];
}

/* SNF generators of a group (of type clgp), or generators of a prime
 * ideal
 */
GEN
member_gen(GEN x)
{
  int t;
  GEN y = get_primeid(x);
  if (y)
  {
    x = cgetg(3,t_VEC);
    x[1] = y[1];
    x[2] = y[2]; return x;
  }
  (void)get_nf(x,&t);
  if (t == typ_GAL)
    return (GEN)x[7];
  x = member_clgp(x);
  if (typ(x)!=t_VEC || lg(x)!=4)
    member_err("gen");
  if (typ(x[1]) == t_COL) return (GEN)x[2]; /* from bnfisprincipal */
  return (GEN) x[3];
}
GEN
member_group(GEN x)
{
  int t; (void)get_nf(x,&t);
  if (t == typ_GAL)
    return (GEN)x[6];
  member_err("group");
  return NULL; /* not reached */
}
GEN
member_orders(GEN x)
{
  int t; (void)get_nf(x,&t);
  if (t == typ_GAL)
    return (GEN)x[8];
  member_err("orders");
  return NULL; /* not reached */
}

GEN
member_a1(GEN x)
{
  if (!is_ell(x)) member_err("a1");
  return (GEN)x[1];
}

GEN
member_a2(GEN x)
{
  if (!is_ell(x)) member_err("a2");
  return (GEN)x[2];
}

GEN
member_a3(GEN x)
{
  if (!is_ell(x)) member_err("a3");
  return (GEN)x[3];
}

GEN
member_a4(GEN x)
{
  if (!is_ell(x)) member_err("a4");
  return (GEN)x[4];
}

GEN
member_a6(GEN x)
{
  if (!is_ell(x)) member_err("a6");
  return (GEN)x[5];
}

GEN
member_b2(GEN x)
{
  if (!is_ell(x)) member_err("b2");
  return (GEN)x[6];
}

GEN
member_b4(GEN x)
{
  if (!is_ell(x)) member_err("b4");
  return (GEN)x[7];
}

GEN
member_b6(GEN x)
{
  if (!is_ell(x)) member_err("b6");
  return (GEN)x[8];
}

GEN
member_b8(GEN x)
{
  if (!is_ell(x)) member_err("b8");
  return (GEN)x[9];
}

GEN
member_c4(GEN x)
{
  if (!is_ell(x)) member_err("c4");
  return (GEN)x[10];
}

GEN
member_c6(GEN x)
{
  if (!is_ell(x)) member_err("c6");
  return (GEN)x[11];
}

GEN
member_j(GEN x)
{
  if (!is_ell(x)) member_err("j");
  return (GEN)x[13];
}

GEN
member_omega(GEN x)
{
  GEN y;

  if (!is_bigell(x)) member_err("omega");
  if (gcmp0((GEN)x[19])) err(talker,"curve not defined over R");
  y=cgetg(3,t_VEC); y[1]=x[15]; y[2]=x[16];
  return y;
}

GEN
member_eta(GEN x)
{
  GEN y;

  if (!is_bigell(x)) member_err("eta");
  if (gcmp0((GEN)x[19])) err(talker,"curve not defined over R");
  y=cgetg(3,t_VEC); y[1]=x[17]; y[2]=x[18];
  return y;
}

GEN
member_area(GEN x)
{
  if (!is_bigell(x)) member_err("area");
  if (gcmp0((GEN)x[19])) err(talker,"curve not defined over R");
  return (GEN)x[19];
}

GEN
member_tate(GEN x)
{
  GEN z = cgetg(3,t_VEC);
  if (!is_bigell(x)) member_err("tate");
  if (!gcmp0((GEN)x[19])) err(talker,"curve not defined over a p-adic field");
  z[1]=x[15];
  z[2]=x[16];
  z[3]=x[17]; return z;
}

GEN
member_w(GEN x)
{
  if (!is_bigell(x)) member_err("w");
  if (!gcmp0((GEN)x[19])) err(talker,"curve not defined over a p-adic field");
  return (GEN)x[18];
}
