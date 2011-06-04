LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y,z),dp;
int k = 7;
poly F = (x*z+y)*(x^k-y^k);
bfct(F);
tst_status(1);$
