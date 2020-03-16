%define name	uno
%define ver	2.0
%define rel	1

Summary: UNO is a simple tool for C source code analysis
Name: %{name}
Version: %{ver}
Release: %{rel}
Source: http://cm.bell-labs.com/cm/cs/what/uno/uno_v22.tar.gz
Patch: %{name}.patch
Copyright: Open Source
Group: Development/Tools
URL: http://cm.bell-labs.com/cm/cs/what/uno/
Packager: Jerry James <james@ittc.ku.edu>
BuildRoot: %{_tmppath}/%{name}-root

%description
UNO is a simple tool for C source code analysis, written in 2001.  It has two
main goals:

  * It is designed to intercept primarily the three most common types of
    software defects:
      o Use of uninitialized variable,
      o Nil-pointer references, and
      o Out-of-bounds array indexing. 

  * It allows for the specification and checking of a broad range of
    user-defined properties that can extend the checking power of the tool in
    an application driven way.  Properties can be specified, for instance, for
    checking lock order disciplines, compliance with user-defined interrupt
    masking rules, rules stipulating that all memory allocated must be freed,
    etc.

%prep
%setup -c
%patch -p1

%build
make

%install
rm -rf %{buildroot}
mkdir -p %{buildroot}%{_bindir}
make install BINDIR=%{buildroot}%{_bindir}
mkdir -p %{buildroot}%{_mandir}/man1
cp Doc/uno.1 %{buildroot}%{_mandir}/man1

%clean
rm -fr $RPM_BUILD_ROOT

%files
%defattr(-, root, root, 0755)
%{_bindir}/*
%{_mandir}/man1/*

%doc Doc/*.pdf
