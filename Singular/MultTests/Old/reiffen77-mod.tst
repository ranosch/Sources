LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring r = 0,(x,y),dp;
poly F = x7+xy6+y7;
bfct(F);
tst_status(1);$
