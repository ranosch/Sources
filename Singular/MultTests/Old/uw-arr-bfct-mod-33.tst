LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y,z),dp;
poly F = 576*x^5*y*z+1200*x^4*y^2*z+840*x^3*y^3*z+240*x^2*y^4*z+24*x*y^5*z+820*x^4*y*z^2+1030*x^3*y^2*z^2+404*x^2*y^3*z^2+50*x*y^4*z^2+273*x^3*y*z^3+200*x^2*y^2*z^3+35*x*y^3*z^3+30*x^2*y*z^4+10*x*y^2*z^4+x*y*z^5;
bfct(F);
tst_status(1);$
