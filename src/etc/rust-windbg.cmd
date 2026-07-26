@echo off
setlocal

set "rustc_cmd=rustc"
if exist "%~dp0trustc.exe" set "rustc_cmd=%~dp0trustc.exe"
if not exist "%~dp0trustc.exe" if exist "%~dp0rustc.exe" set "rustc_cmd=%~dp0rustc.exe"

for /f "delims=" %%i in ('"%rustc_cmd%" --print=sysroot') do set rustc_sysroot=%%i

set rust_etc=%rustc_sysroot%\lib\rustlib\etc

windbg -c ".nvload %rust_etc%\intrinsic.natvis; .nvload %rust_etc%\liballoc.natvis; .nvload %rust_etc%\libcore.natvis;" %*
