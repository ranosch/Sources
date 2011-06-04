LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y,z),dp;
int p,q = 4,5;
poly F = (x*y+z)*(y^p+z^q+y*z^(q-1));
bfct(F);
tst_status(1);$
