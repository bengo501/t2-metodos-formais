@echo off
setlocal
chcp 65001 >nul
rem roda a partir da pasta onde este .bat esta localizado
cd /d "%~dp0"

echo =============================
echo  1) verificando Pilha.dfy 
echo =============================
dafny verify "Pilha.dfy"
if errorlevel 1 (
    echo.
    echo [ERRO] a verificacao falhou. abortando antes de executar.
    echo.
    pause
    exit /b 1
)

echo.
echo ====================================================
echo  2) compilando e executando ^(artefatos em build\^)
echo ====================================================
dafny build "Pilha.dfy" --no-verify --output "build\Pilha"
"build\Pilha.exe"

echo.
pause
