@echo off
setlocal
chcp 65001 >nul
cd /d "%~dp0"

echo ===============================================
echo   instalador de dependencias - t2 - Dafny + Z3
echo ===============================================
echo.

rem 1) verifica o .NET SDK
where dotnet >nul 2>nul
if errorlevel 1 (
    echo [ERRO] .NET SDK nao encontrado
    echo        instale o .NET 8 SDK em:
    echo        https://dotnet.microsoft.com/download/dotnet/8.0
    echo        depois rode este instalador novamente
    echo.
    pause
    exit /b 1
)
echo [OK] .NET SDK encontrado
echo.

rem garante o dafny no PATH desta sessao
set "PATH=%PATH%;%USERPROFILE%\.dotnet\tools"

rem 2) instala o Dafny 4.11.0 (se ainda nao estiver instalado)
set "DAFNY_OK="
for /f "tokens=*" %%v in ('dafny --version 2^>nul') do (
    echo %%v | findstr /b "4.11.0" >nul && set "DAFNY_OK=1"
)
if defined DAFNY_OK (
    echo [OK] Dafny 4.11.0 ja instalado
) else (
    echo Instalando o Dafny 4.11.0 ...
    dotnet tool install --global Dafny --version 4.11.0
    if errorlevel 1 dotnet tool update --global Dafny --version 4.11.0
)
echo.

rem 3) baixa e instala o Z3 4.12.1 onde o Dafny o procura
set "Z3DIR=%USERPROFILE%\.dotnet\tools\.store\dafny\4.11.0\dafny\4.11.0\tools\net8.0\any\z3\bin"
if exist "%Z3DIR%\z3-4.12.1.exe" (
    echo [OK] Z3 4.12.1 ja instalado
) else (
    echo baixando e instalando o Z3 4.12.1 ^(pode levar alguns segundos^)
    powershell -NoProfile -ExecutionPolicy Bypass -Command "$ErrorActionPreference='Stop'; $zip=Join-Path $env:TEMP 'z3-4.12.1.zip'; Invoke-WebRequest -Uri 'https://github.com/Z3Prover/z3/releases/download/z3-4.12.1/z3-4.12.1-x64-win.zip' -OutFile $zip; $tmp=Join-Path $env:TEMP 'z3-4.12.1-extract'; if(Test-Path $tmp){Remove-Item -Recurse -Force $tmp}; Expand-Archive -Path $zip -DestinationPath $tmp -Force; $exe=Get-ChildItem $tmp -Recurse -Filter z3.exe | Select-Object -First 1 -ExpandProperty FullName; $dest=Join-Path $env:USERPROFILE '.dotnet\tools\.store\dafny\4.11.0\dafny\4.11.0\tools\net8.0\any\z3\bin'; New-Item -ItemType Directory -Force -Path $dest | Out-Null; Copy-Item $exe (Join-Path $dest 'z3-4.12.1.exe') -Force; Write-Host '[OK] Z3 instalado.'"
    if errorlevel 1 (
        echo [ERRO] falha ao baixar/instalar o Z3
        echo        verifique sua conexao com a internet e tente de novo
        echo.
        pause
        exit /b 1
    )
)
echo.

rem 4) teste rapido 
if exist "Pilha.dfy" (
    echo testando a verificacao do Pilha.dfy ...
    dafny verify "Pilha.dfy"
)
echo.
echo ============================================================
echo   instalacao concluida!
echo   agora use:  verificar_e_executar.bat
echo   ou rode:    dafny verify Pilha.dfy
echo ============================================================
echo.
pause
