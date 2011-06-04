LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y,z),dp;
poly F = -x^2*y^2*z+x^2*y*z^2-x*y^2*z^2+x*y*z^3;
bfct(F);
tst_status(1);$
