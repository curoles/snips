call %~dp0\..\..\..\config\user\win\env.bat


%UNIX_TOOLS%\make  -f %~dp0/../../hwlib/Dff/test/sv/Makefile

if errorlevel 1 (
   echo Test failed with error code: %errorlevel%
   exit /b %errorlevel%
)

exit /b 0
