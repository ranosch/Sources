LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y,z),dp;
poly F = -12*x^4*y^2*z+2*x^3*y^3*z+2*x^2*y^4*z-12*x^4*y*z^2+21*x^3*y^2*z^2-x^2*y^3*z^2-2*x*y^4*z^2+19*x^3*y*z^3-11*x^2*y^2*z^3-x*y^3*z^3-8*x^2*y*z^4+2*x*y^2*z^4+x*y*z^5;
bfct(F);
tst_status(1);$
