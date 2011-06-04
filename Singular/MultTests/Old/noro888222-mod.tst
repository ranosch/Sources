LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring r = 0,(x,y,z),dp;
poly F = x^8 + y^8 + z^8 + x^2 * y^2 * z^2;
bfct(F);
tst_status(1);$
