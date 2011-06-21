#! /bin/bash

PWD=`pwd`
BRANCH="spielwiese"

# configure' options
CFGOPTIONS="--with-gmp=yes"

# computer specific make options: e.g. -j9
DEFMKOPTIONS="-j2"


D="`hostname`.`date +%y.%m.%d.%H.%M.%S`"

# we try to use log instead of consequent --quiet
LOG="$PWD/$D.log"

# tempdir (absolute path!)
SW="$PWD/$D"

# use out of tree building, with clean GIT repository being at:
GIT="$SW/GIT"

# build in...
BLD="$SW/BUILD"

# install to...
OUT="$SW/INSTALL"







# log or no log?
echo >> $LOG || LOG="/dev/null"

echo "DATE: `date`" >> $LOG
echo "HOST: `hostname`" >> $LOG
echo "SYSTEM: `uname -a`" >> $LOG 


echo "Looking for make... " >> $LOG 
echo "Using [${MAKE:=make}] with [${MKOPTIONS:=$DEFMKOPTIONS}]" >> $LOG;


echo "Creating empty tempdir: $SW" >> $LOG
[ -d "$SW" ] && { echo "Error: $SW exists... cleaning up..." >> $LOG; mv -f "$SW" "$SW.moved" 1>> $LOG 2>&1 && { rm -f -R "$SW.moved" 1>> $LOG 2>&1 || echo "Error: could not remove '$SW.moved'"; } || { echo "Error: could not rename '$SW' -> '$SW.moved'"; exit 1; }; }

mkdir -p "$SW" || { echo "Error: cannot create tempdir: $SW" >> $LOG;  exit 1; }

[ -d "$SW" ] || { echo "Error: cannot find tempdir '$SW'" >> $LOG; CleanUp; exit 1; } 
[ ! -x "$SW" ] && { chmod u+rwx $SW 1>> $LOG 2>&1 || { echo "Error: cannot set rxw permissions for $SW" >> $LOG;  exit 1; }; }



CleanUp() 
{
  echo "Cleanup upno error....?" >> $LOG

###### no cleanup upon an error...
#  echo "Deleting tempdir: $SW" >> $LOG
#  rm -f -R "$SW" 1>> $LOG 2>&1
}

CleanUpOk() 
{
  echo "Deleting tempdir: $SW" >> $LOG

#  rm -f -R "$SW" 1>> $LOG 2>&1
}

Prepare()
{
  echo "Clonning git repo into '$GIT'... " >> $LOG
  git clone -v -b $BRANCH --depth 1 -- git://git.berlios.de/singular "$GIT" 1>> $LOG 2>&1 || { echo "Error: cannot git clone..." >> $LOG; CleanUp; exit 1; } 

  cd "$GIT"  || { echo "Error: cannot cd to the tempdir: $GIT" >> $LOG; CleanUp; exit 1; } 

  # latest commit?
  git log -1 HEAD >> $LOG 

  [ -x ./for_Hans_with_love.sh ] || { echo "Error: cannot find './for_Hans_with_love.sh '" >> $LOG; CleanUp; exit 1; } 

  echo "Generating configure... " >> $LOG
  ./for_Hans_with_love.sh 1>> $LOG 2>&1  || { echo "Error: cannot run 'for_Hans_with_love.sh'" >> $LOG; CleanUp; exit 1; } 
}

Build()
{
  [ -f $GIT/configure ] || { echo "Error: could not find '$GIT/configure'" >> $LOG; return 1; } 

  echo "Configuring with '$GIT/configure \"$CFGOPTIONS\" \"$@\"'... " >> $LOG
  $GIT/configure $CFGOPTIONS "$@" 1>> $LOG 2>&1  || { echo "Error: could not run './configure \"$CFGOPTIONS\" \"$@\"'" >> $LOG; return 1; } 

  echo "Making with '$MAKE $MKOPTIONS'... " >> $LOG
  $MAKE $MKOPTIONS 1>> $LOG 2>&1  || { echo "Error: could not run 'make \"$MKOPTIONS\"'" >> $LOG; return 1; } 
}

Check()
{
  echo "Checking... " >> $LOG
  $MAKE -k -i check 1>> $LOG 2>&1

  echo "Test Result: $?" >> $LOG

  [ -x libpolys/tests ] && { echo "The content of the test directory: " >> $LOG; ls -la libpolys/tests 1>> $LOG 2>&1; }
}


Reset()
{
  cd "$GIT"
  echo "git reset/clean to the untouched state... " >> $LOG
  git reset --hard HEAD 1>> $LOG 2>&1 || echo "Error: could not git reset to HEAD..." >> $LOG 
  git clean -f -d -x 1>> $LOG 2>&1 || echo "Error: could not git clean..." >> $LOG 

##  #should be VERY clean now...
##  git status -uall  >> $LOG
}



BuildInstallTest()
{
  EXT="$1"
  shift 
  echo "Creating empty tempdir: '$BLD.$EXT'" >> $LOG
  mkdir -p "$BLD.$EXT" || { echo "Error: cannot create tempdir: $BLD" >> $LOG; CleanUp; exit 1; }
  cd "$BLD.$EXT" || { echo "Error: cannot cd to the tempdir: $BLD.$EXT" >> $LOG; CleanUp; exit 1; } 

  echo "Trying the [$EXT] version with [$@]... " >> $LOG
  Build "--prefix=$OUT.$EXT" "$@" && Check || { echo "Error: could not build with '--prefix=$OUT.$EXT'" >> $LOG; exit 1; }

  echo "Installing into '$OUT.$EXT'... " >> $LOG
  make install 1>> $LOG 2>&1 

  # let's inspect the installation now:
  cd "$OUT.$EXT" || { echo "Error: cannot cd to the instalation dir: $OUT.$EXT" >> $LOG; CleanUp; exit 1; } 

  echo "Content of '$OUT.$EXT'... " >> $LOG
  ls -R "$OUT.$EXT" 1>> $LOG 2>&1 

  # let's test the installation using the standalone test:
  echo "Going to '$OUT.$EXT/bin'... " >> $LOG
  cd "$OUT.$EXT/bin" || { echo "Error: cannot cd to '$OUT.$EXT/bin'" >> $LOG; CleanUp; exit 1; } 

  echo "Copying '$GIT/standalone.test' to '$OUT.$EXT/bin'... " >> $LOG
  cp -vfR $GIT/standalone.test/* "$OUT.$EXT/bin/" 1>> $LOG 2>&1 || { echo "Error: could not copy standalone.test" >> $LOG; CleanUp; exit 1; }

  echo "Building the standalone test... " >> $LOG
  ./mk 1>> $LOG 2>&1 || { echo "Error: could not build standalone.test" >> $LOG; CleanUp; exit 1; } 

  echo "Running the test... " >> $LOG
  ./test 1>> $LOG 2>&1 || { echo "Error: could not run standalone.test" >> $LOG; CleanUp; exit 1; } 
}

########### main code ############

echo "Prepearing the build system... " >> $LOG
Prepare


# test two cases dynamic & static:
#  --enable-p-procs-static Enable statically compiled p_Procs-modules
#  --enable-p-procs-dynamic Enable dynamically compiled p_Procs-modules

echo "Trying the default version... " >> $LOG
BuildInstallTest "default" 1>> $LOG 2>&1 || { echo "Error: could not do the default version... " >> $LOG; CleanUp; } 

echo "Trying static version with all features disabled... " >> $LOG
BuildInstallTest "minimal" "--disable-arith-rings" "--disable-factory" "--disable-plural" "--disable-p-procs-dynamic" "--enable-p-procs-static" 1>> $LOG 2>&1 || { echo "Error: could not do the minimal version... " >> $LOG; CleanUp; } 


cd $PWD || { CleanUp; exit 1; } 

CleanUpOk || exit 1

exit 0




