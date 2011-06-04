LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y,z),dp;
poly F = 3*x^3*y*z+5*x^2*y^2*z+2*x*y^3*z+4*x^2*y*z^2+3*x*y^2*z^2+x*y*z^3;
bfct(F);
tst_status(1);$
