LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y,z,w),dp;
int p = 2;
int q= 3;
poly F = (z^p + w^q)*(p*z^(p-1)*x + q*w^(q-1)*y);
bfct(F);
tst_status(1);$
