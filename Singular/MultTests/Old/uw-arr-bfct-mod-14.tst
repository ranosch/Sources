LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y,z),dp;
poly F = 24*x*y^5*z+50*x*y^4*z^2+35*x*y^3*z^3+10*x*y^2*z^4+x*y*z^5;
bfct(F);
tst_status(1);$
