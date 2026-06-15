@echo off
setlocal
chcp 65001 >nul
rem Roda a partir da pasta onde este .bat esta localizado
cd /d "%~dp0"

echo ===========================================
echo  Verificando Pilha.dfy ...
echo ===========================================
dafny verify "Pilha.dfy" --solver-path "C:\Users\bengo\z3-4.12.1\z3-4.12.1-x64-win\bin\z3.exe"

echo.
echo ===========================================
echo  Executando Pilha.dfy ...
echo ===========================================
dafny run "Pilha.dfy" --solver-path "C:\Users\bengo\z3-4.12.1\z3-4.12.1-x64-win\bin\z3.exe"

echo.
pause
