REM Script to create RPPRO source code archive
REM author: Igor Lesik 2013

setlocal

call %~dp0\..\..\..\config\user\win\env.bat

REM directory to be archived
set SRCDIR=%1

REM archive name
set ARNAME=RPPRO

set HOST=%COMPUTERNAME%

for /f %%i in ('%UNIX_TOOLS%\date +%%F_%%H') do set STAMP=%%i

%UNIX_TOOLS%\zip -r %ARNAME%-%STAMP%_%HOST%.zip %SRCDIR%
