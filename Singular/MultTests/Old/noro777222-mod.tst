LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring r = 0,(x,y,z),dp;
poly F = x^7 + y^7 + z^7 + x^2 * y^2 * z^2;
bfct(F);
tst_status(1);$
