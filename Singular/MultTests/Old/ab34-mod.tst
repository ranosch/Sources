LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y,z,w),dp;
int p =3;
int q= 4;
poly F = (z^p + w^q)*(p*z^(p-1)*x + q*w^(q-1)*y);
F;
bfct(F);
tst_status(1);$
