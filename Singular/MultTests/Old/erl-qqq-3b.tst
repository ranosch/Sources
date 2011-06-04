LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x(1..5)),dp;
poly F = x(5)*x(2)+x(4)*x(5)+x(1)*x(5)+x(1)*x(2)*x(5)+x(1)*x(4)+x(1)*x(4)*x(3)+x(1)*x(3)+x(4)*x(2)*x(3)+x(4)*x(3)+x(4)*x(2)*x(1)+x(1)*x(2)+x(4)*x(2)*x(5)+x(5)*x(3)*x(1)+x(3)*x(2)+x(5)*x(2)*x(3)+x(5)*x(4)*x(3);
bfct(F);
tst_status(1);$
