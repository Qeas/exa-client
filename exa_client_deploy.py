#!/usr/bin/python3
# -*- coding: utf-8 -*-

# ******************************************************************************
#
#                                --- WARNING ---
#
#   This work contains trade secrets of DataDirect Networks, Inc.  Any
#   unauthorized use or disclosure of the work, or any part thereof, is
#   strictly prohibited.  Copyright in this work is the property of DataDirect.
#   Networks, Inc. All Rights Reserved. In the event of publication, the.
#   following notice shall apply: (C) 2019, DataDirect Networks, Inc.
#
# ******************************************************************************

import sys
import argparse
import xml.etree.ElementTree as ET
import collections
from subprocess import Popen, PIPE, STDOUT
import os
import shutil
import glob
import logging
import logging.handlers
import datetime
import re
import platform
import time

logger = logging.getLogger(__name__)
VERSION = "6.2.1"

supported_kernels_centos = ["3.10.0", "4.18.0", "5.14.0"]
supported_kernels_ubuntu = ["4.15.0", "5.3.0", "5.4.0", "5.15.0"]
supported_dkms_packages = [
    "el79",
    "el85",
    "el86",
    "el87",
    "el88",
    "el91",
    "el92",
    "ubuntu1804",
    "ubuntu2004",
    "ubuntu2204",
]
DGX_CPU_NPARTITIONS = {"DGX-1": "20", "DGX-2": "24", "DGX-A100": "32"}

ARP_INFO = {"accept_local": 1, "arp_announce": 2, "rp_filter": 0}
NICS_ARP_INFO = {"arp_ignore": 1, "arp_filter": 0, "arp_announce": 2, "rp_filter": 0}

RHEL_DISTROS = ["rhel", "redhat", "centos", "almalinux", "rocky"]

CHECK = "1"
INSTALL = "2"
CONFIGURE = "3"
REMOVE = "4"
LIST_MOUNT = "5"
EXIT = "6"


PYTHON_TOOLS = ["python3-netifaces", "python3-netaddr"]
DEVELOPMENT_TOOLS_CENTOS = [
    "attr",
    "libselinux-devel",
    "expect",
    "sg3_utils",
    "libyaml",
    "libyaml-devel",
    "binutils-devel",
    "python3-netifaces",
    "python3-netaddr",
    "elfutils-libelf-devel",
    "rsync",
    "kernel-rpm-macros",
    "keyutils-libs",
    "keyutils-libs-devel",
    "json-c-devel",
    "libmount-devel",
    "openssl-devel",
]
DEVELOPMENT_TOOLS_UBUNTU = [
    "libtool",
    "automake",
    "wget",
    "git",
    "make",
    "dpkg-dev",
    "bc",
    "libselinux-dev",
    "fio",
    "ed",
    "libssl-dev",
    "module-assistant",
    "libreadline-dev",
    "debhelper",
    "dpatch",
    "libsnmp-dev",
    "quilt",
    "rsync",
    "libyaml-dev",
    "build-essential",
    "debhelper",
    "devscripts",
    "fakeroot",
    "kernel-wedge",
    "libudev-dev",
    "keyutils",
    "libkeyutils1",
    "libkeyutils-dev",
    "krb5-multidev",
    "libgssapi-krb5-2",
    "libkrb5-3",
    "libkrb5-dev",
    "kmod",
    "sg3-utils",
    "attr",
    "lsof",
    "mpi-default-dev",
    "mpi-default-bin",
    "pkg-config",
    "systemd",
    "python2.7",
    "libelf-dev",
    "python3-netaddr",
    "python3-netifaces",
    "libtool-bin",
    "python3-dev",
    "python3-distutils",
    "bison",
    "flex",
    "libjson-c-dev",
    "libmount-dev",
]

LOG_ERROR_LEVEL = 4
LOG_WARNING_LEVEL = 3
LOG_INFO_LEVEL = 2
LOG_DEBUG_LEVEL = 1


class DeployerException(Exception):
    """Class for exceptions during upgrade procedure."""

    pass


class Updater(object):
    """Class for ES release upgrade procedure."""

    def __init__(
        self,
        lustre_source,
        lnets,
        cpu_npartitions,
        emf_ip,
        dkms,
        dry_run=False,
        force=False,
        install=False,
        remove=False,
        list_mount=False,
        verbosity=1,
        configure=False,
        skip_eth_tuning=False,
        skip_ro_tuning=False,
        yes=False,
        skip_persistent=False,
        disable_o2ib=False,
    ):
        """Basic initialization."""

        self._update_dir = None
        self._lustre_src = lustre_source
        self._lnets = lnets.split(";") if lnets else None
        self._cpu_npartitions = cpu_npartitions
        self._linux_distribution_name = None
        self._linux_distribution = None
        self._emf_ip = emf_ip
        self._dkms = dkms
        self._dry_run = dry_run
        self._install = install
        self._configure = configure
        self._remove = remove
        self._list_mount = list_mount
        self._force = force
        self._verbosity = verbosity
        self._script_directory = None
        self._new_version = None
        self._target_kernel = None
        self._clean_builddir = True
        self._dgx_system = None
        self._debs_dump = []
        self._nics = set()
        self._mofed_installed = False
        self._skip_eth_tuning = skip_eth_tuning
        self._skip_ro_tuning = skip_ro_tuning
        self._yes = yes
        self._skip_persistent = skip_persistent
        self._emf_endpoint = None
        self._disable_o2ib = disable_o2ib

    def linux_distribution(self, full_distribution_name=False):
        # Try in that order:
        # - platform
        # - distro
        # - install distro through pip and retry
        # - find OS manually

        try:
            self._print_info(
                "Try to find linux_distribution via platform", LOG_INFO_LEVEL
            )
            distrib = platform.linux_distribution(
                full_distribution_name=full_distribution_name
            )

            # We can't trust debian output as
            # platform.linux_distribution is bugged
            # on non-patched version of ubuntu
            # See https://stackoverflow.com/questions/33996196/
            if "debian" in distrib[0].lower():
                self._print_info(
                    "Found debian with platform but can't be trusted", LOG_INFO_LEVEL
                )
                raise
            else:
                return distrib

        except Exception:
            try:
                self._print_info(
                    "Try to find linux_distribution via distro", LOG_INFO_LEVEL
                )
                import distro

                # From distro github:
                # linux_distribution is deprecated
                # * ``id_name``:  If *full_distribution_name* is false, the result of
                # :func:`distro.id`. Otherwise, the result of :func:`distro.name`.
                return (
                    distro.name() if full_distribution_name else distro.id(),
                    distro.version(),
                    distro.codename(),
                )

            except Exception:
                try:
                    self._print_info(
                        "Try to install distro & find linux_distribution",
                        LOG_INFO_LEVEL,
                    )
                    ret, out = self._run_cmd(
                        [sys.executable, "-m", "pip", "install", "distro"]
                    )
                    import distro

                    return (
                        distro.name() if full_distribution_name else distro.id(),
                        distro.version(),
                        distro.codename(),
                    )

                except Exception as e:
                    try:
                        self._print_info(
                            "Try to find linux_distribution manually", LOG_INFO_LEVEL
                        )
                        distrib = get_distrib_from_os_release_file(
                            full_distribution_name=full_distribution_name
                        )
                        if distrib != None:
                            return distrib
                    except Exception:
                        pass

                    if type(e) is ImportError:
                        print(
                            "Unable to import distro. Can't determine your linux distribution\n"
                            "Please install distro package for your distribution\n"
                            "e.g: apt install python3-distro -y || pip3 install distro\n"
                        )
                    else:
                        print(e)
                        print(
                            "Can't determine the linux distribution\n"
                            "Please contact the support to report this bug\n"
                        )

                exit(1)

    def _run_cmd(self, args, dry_run=False, **kwargs):
        """Run command line."""
        cmd = " ".join(args)
        if dry_run:
            print("$", cmd)
            return 0, ""

        self._print_info("Running '{0}' command".format(cmd), LOG_INFO_LEVEL)
        process = Popen(
            cmd,
            bufsize=0,
            close_fds=True,
            stdout=PIPE,
            stderr=STDOUT,
            shell=True,
            **kwargs
        )
        std_out = list()
        while True:
            line = process.stdout.readline().decode(errors="replace")
            if line.rstrip() != b"" and not process.poll():
                std_out.append(line)
                self._print_info(line.rstrip(), LOG_INFO_LEVEL)
            if line == "" and process.poll() is not None:
                break
        return_code = process.returncode
        output = "".join(std_out)
        return return_code, output

    def _print_info(self, message, log_level=LOG_INFO_LEVEL, log_to_console=False):
        """Print message to log file and console."""
        try:
            m = message.encode("utf-8", "replace").decode()
        except:
            m = message
        if log_to_console or self._verbosity > 0:
            print(m)
        if log_level == LOG_DEBUG_LEVEL:
            logger.debug(m)
        elif log_level == LOG_INFO_LEVEL:
            logger.info(m)
        elif log_level == LOG_WARNING_LEVEL:
            logger.warning(m)
        elif log_level == LOG_ERROR_LEVEL:
            logger.error(m)
            raise DeployerException()

    def _is_rpm_installed(self, rpm_name):
        return not self._run_cmd(["rpm", "-q", rpm_name, ">/dev/null", "2>&1"])[0]

    def _is_deb_installed(self, deb_name):
        return not self._run_cmd(["dpkg-query", "-s", deb_name, ">/dev/null", "2>&1"])[
            0
        ]

    def _init_logger(self):
        """Initialize logger."""

        logger.setLevel(logging.INFO)

        # Create a syslog handler
        log_syslog_handler = logging.handlers.SysLogHandler("/dev/log")

        # Create a logging format.
        formatter = logging.Formatter("%(filename)s - %(levelname)s: %(message)s")
        log_syslog_handler.setFormatter(formatter)

        # Add the handler to the logger.
        logger.addHandler(log_syslog_handler)

        # Create a stream handler
        log_stream_handler = logging.StreamHandler(sys.stdout)
        log_stream_handler.setLevel(logging.WARNING)

        # Add handler to the logger
        logger.addHandler(log_stream_handler)

    def _get_script_dir_path(self):
        """Get path of directory in which script was ran."""

        self._print_info("Getting script's directory path.")

        self._script_directory = os.path.dirname(os.path.abspath(__file__))

        self._print_info(
            "Script's directory path is: {0}".format(self._script_directory)
        )

    def _make_upd_dir(self):
        """Create directory for temporary files."""

        self._print_info("Create directory for temporary files")

        if not self._dry_run:
            if os.path.exists(self._update_dir):
                shutil.rmtree(self._update_dir)
            os.makedirs(self._update_dir)
            if not os.path.exists("/opt/ddn/exascaler/"):
                self._print_info(
                    "Create a directory for final packages in /opt/ddn/exascaler/"
                )
                os.makedirs("/opt/ddn/exascaler/")

        self._print_info("Temporary directory path is '{0}'".format(self._update_dir))

    def _remove_upd_dir(self):
        """Remove directory for temporary files."""

        self._print_info("Remove directory for temporary files")

        if not self._dry_run and os.path.exists(self._update_dir):
            shutil.rmtree(self._update_dir)

        self._print_info("Temporary directory path was cleaned.")

    def initialize(self):
        """Some initialization steps."""

        self._init_logger()
        self._get_script_dir_path()
        self._update_dir = os.path.join(self._script_directory, "builddir")

    def _check_distribution(self):
        """Check linux distribution"""
        self._linux_distribution = self.linux_distribution(True)
        self._linux_distribution_name = self.linux_distribution(False)[0].lower()

        if self._linux_distribution_name not in ["ubuntu"] + RHEL_DISTROS:
            exit(
                "\nThis script is only supported on Ubuntu/RHEL-like Operating System. Exiting.\n"
            )

        if self._linux_distribution_name == "ubuntu":
            if platform.release().split("-")[0] not in supported_kernels_ubuntu:
                if not yes_no_query(
                    "\nThe script is not supported on the kernel {}"
                    "\nDo you want to continue".format(platform.release()),
                    "yes",
                    self._yes,
                ):
                    exit()
        elif self._linux_distribution_name in RHEL_DISTROS:
            if platform.release().split("-")[0] not in supported_kernels_centos:
                if not yes_no_query(
                    "\nThe script is not supported on the kernel {}"
                    "\nDo you want to continue".format(platform.release()),
                    "yes",
                    self._yes,
                ):
                    exit()

    def _dump_debs_list(self):
        ret, out = self._run_cmd(["dpkg", "-l"])
        if ret != 0:
            self._print_info("Unable to get debs' list.", LOG_ERROR_LEVEL)
        self._debs_dump = out.splitlines()

    def _prepare_python_env(self):
        self._print_info("Preparing python environment...", LOG_INFO_LEVEL)

        cmds_to_execute = []

        if self._linux_distribution_name == "ubuntu":
            cmd_header = ["DEBIAN_FRONTEND=noninteractive"]
            pkg_manager_cmd = cmd_header + ["apt-get", "-y", "install"]
            cmds_to_execute.append(["apt-get", "update"])
            cmds_to_execute.append(pkg_manager_cmd + PYTHON_TOOLS)

        else:
            pkg_manager_cmd = ["yum", "-y", "install"]
            cmds_to_execute.append(pkg_manager_cmd + PYTHON_TOOLS)

        for cmd in cmds_to_execute:
            try:
                # No dry-run since we need the modules in order to display --dry-run
                # If we have reached to this point, import has failed
                ret, _ = self._run_cmd(cmd)
                if ret != 0:
                    raise Exception("exit code {}".format(ret))
            except Exception as e:
                self._print_info(e, LOG_INFO_LEVEL)
                self._print_info(
                    "Unable to prepare python environment. Failed command: {}".format(
                        " ".join(cmd)
                    ),
                    LOG_WARNING_LEVEL,
                )
        self._print_info("Preparing python environment... Done", LOG_INFO_LEVEL)

    def _prepare_build_env(self):
        self._print_info("Preparing build environment...", LOG_INFO_LEVEL, True)
        if self._linux_distribution_name == "ubuntu":
            cmds_to_execute = []
            if self._dkms:
                cmds_to_execute.append(
                    ["rm", "-f", "/etc/apt/sources.list.d/exascaler-client.list"]
                )
            cmd_header = ["DEBIAN_FRONTEND=noninteractive"]
            apt_install = cmd_header + ["apt-get", "-y", "install"]
            cmds_to_execute.append(["apt-get", "update"])
            cmds_to_execute.append(apt_install + ["apt-utils"])
            cmds_to_execute.append(apt_install + DEVELOPMENT_TOOLS_UBUNTU)
            if self._linux_distribution[1][0] == "2":
                cmds_to_execute.append(apt_install + ["golang", "libpam0g-dev"])
            kernel_headers = "linux-headers-{0}".format(self._target_kernel)
            cmds_to_execute.append(apt_install + [kernel_headers])
            kernel_headers_generic = "linux-headers-generic"
            cmds_to_execute.append(apt_install + [kernel_headers_generic])
            for cmd in cmds_to_execute:
                ret, _ = self._run_cmd(cmd, self._dry_run)
                if ret != 0:
                    self._print_info(
                        "Unable to prepare build environment. Failed command: {}".format(
                            " ".join(cmd)
                        ),
                        LOG_ERROR_LEVEL,
                    )
        else:
            yum_base_cmd = ["yum", "-y"]
            cmds_to_execute = []

            if self._dkms:
                cmds_to_execute.append(
                    ["rm", "-f", "/etc/yum.repos.d/exascaler-client.repo"]
                )
            dev_tools_install_cmd = ["group", "install", '"Development Tools"']
            cmds_to_execute.append(yum_base_cmd + dev_tools_install_cmd)

            # This will fail on CentOS7 node
            if not self._is_rpm_installed("libyaml-devel"):
                rhel_distro = self._linux_distribution[1][0]
                if rhel_distro in ("8", "9"):
                    install_libyaml_devel = [
                        *yum_base_cmd,
                        "--disablerepo=*",
                        "--enablerepo=powertools",
                        "install",
                        "libyaml-devel",
                        "||",
                        *yum_base_cmd,
                        "--disablerepo=*",
                        "--enablerepo=PowerTools",
                        "install",
                        "libyaml-devel",
                        "||",
                        *yum_base_cmd,
                        "--disablerepo=*",
                        "--enablerepo=crb",
                        "install",
                        "libyaml-devel",
                        "||",
                        *yum_base_cmd,
                        "--disablerepo=*",
                        "--enablerepo=codeready-builder-for-rhel-{}-x86_64-rpms".format(
                            rhel_distro
                        ),
                        "install",
                        "libyaml-devel",
                        "||",
                        *yum_base_cmd,
                        "install",
                        "libyaml-devel",
                    ]
                    cmds_to_execute.append(install_libyaml_devel)

            if not self._is_rpm_installed("libmount-devel"):
                if self._linux_distribution[1][0] in ("8", "9"):
                    install_libmount_devel = [
                        *yum_base_cmd,
                        "--enablerepo=powertools",
                        "install",
                        "libmount-devel",
                        "||",
                        *yum_base_cmd,
                        "--enablerepo=PowerTools",
                        "install",
                        "libmount-devel",
                        "||",
                        *yum_base_cmd,
                        "--enablerepo=AppStream",
                        "install",
                        "libmount-devel",
                        "||",
                        *yum_base_cmd,
                        "--enablerepo=codeready-builder-for-rhel-8-x86_64-rpms",
                        "install",
                        "libmount-devel",
                        "||",
                        *yum_base_cmd,
                        "--enablerepo=rhel-9-for-x86_64-appstream-rpms",
                        "install",
                        "libmount-devel",
                        "||",
                        *yum_base_cmd,
                        "install",
                        "libmount-devel",
                    ]
                    cmds_to_execute.append(install_libmount_devel)

            if not self._is_rpm_installed("json-c-devel"):
                if self._linux_distribution[1][0] == "9":
                    install_json_c_devel = [
                        *yum_base_cmd,
                        "--enablerepo=crb",
                        "install",
                        "json-c-devel",
                        "||",
                        *yum_base_cmd,
                        "--enablerepo=rhel-8-for-x86_64-appstream-rpms",
                        "install",
                        "json-c-devel",
                        "||",
                        *yum_base_cmd,
                        "--enablerepo=codeready-builder-for-rhel-9-x86_64-rpms",
                        "install",
                        "json-c-devel",
                        "||",
                        *yum_base_cmd,
                        "install",
                        "json-c-devel",
                    ]
                    cmds_to_execute.append(install_json_c_devel)

            if not self._is_rpm_installed("epel-release"):
                rhel_release = self._linux_distribution[1][0]
                install_epel_release = [
                    *yum_base_cmd,
                    "install",
                    "https://dl.fedoraproject.org/pub/epel/epel-release-latest-{}.noarch.rpm".format(
                        rhel_release
                    ),
                    "||",
                    *yum_base_cmd,
                    "install",
                    "epel-release",
                ]
                cmds_to_execute.append(install_epel_release)

            kernel_devel_pkg = "kernel-devel-" + self._target_kernel

            kernel_headers = "kernel-headers-" + self._target_kernel

            install_cmd = ["install"] + DEVELOPMENT_TOOLS_CENTOS + [kernel_devel_pkg]

            cmds_to_execute.append(yum_base_cmd + install_cmd)

            # This one might fail, we will check later with self.check_rhel_kernel_headers() is the headers are OK
            install_cmd = ["install"] + [kernel_headers] + ["|| true"]

            cmds_to_execute.append(yum_base_cmd + install_cmd)

            if self._linux_distribution[1][0] == "9":
                install_cmd = ["install", "kernel-abi-stablelists"]
            else:
                install_cmd = ["install", "kernel-abi-whitelists", "python2"]

            cmds_to_execute.append(yum_base_cmd + install_cmd)

            for cmd in cmds_to_execute:
                ret, _ = self._run_cmd(cmd, self._dry_run)
                if ret != 0:
                    self._print_info(
                        "Unable to prepare build environment. Failed command: {}".format(
                            " ".join(cmd)
                        ),
                        LOG_ERROR_LEVEL,
                    )
            # Check kernel header
            self.check_rhel_kernel_headers()
        self._print_info("Preparing build environment... Done", LOG_INFO_LEVEL, True)

    def _install_fscrypt(self):
        cmd = None
        if self._linux_distribution_name == "ubuntu":
            distribution = "ubuntu{0}04".format(self._linux_distribution[1][0:2])
            cmd = ["apt-get", "-y", "install", "./fscrypt*.deb"]
        else:
            if self._linux_distribution[1][0] in ("8", "9"):
                distribution = "el{0}".format(self._linux_distribution[1][0])
                cmd = ["yum", "-y", "localinstall", "fscrypt*.rpm"]

        if cmd is not None:
            fscrypt_pkg_dir = os.path.join(
                self._script_directory, "fscrypt", distribution
            )

            ret = -1
            try:
                ret, _ = self._run_cmd(cmd, self._dry_run, cwd=fscrypt_pkg_dir)
            except FileNotFoundError as f:
                print("Fscrypt package not found: {}".format(f.filename))

            if ret != 0:
                self._print_info(
                    "Unable to install the fscrypt package", LOG_WARNING_LEVEL
                )

    def _install_lipe(self):
        cmd = None
        if self._linux_distribution_name == "ubuntu":
            distribution = "ubuntu{0}04".format(self._linux_distribution[1][0:2])
            cmd = ["apt-get", "-y", "install", "./lipe*.deb"]
        else:
            distribution = "el{0}".format(self._linux_distribution[1][0])
            cmd = ["yum", "-y", "localinstall", "lipe*.rpm"]

        if cmd is not None:
            lipe_pkg_dir = os.path.join(self._script_directory, "lipe", distribution)
            ret = -1
            try:
                ret, _ = self._run_cmd(cmd, self._dry_run, cwd=lipe_pkg_dir)
            except FileNotFoundError as f:
                print("\nlipe-lpcc package not found: {}".format(f.filename))

            if ret != 0:
                self._print_info(
                    "Unable to install the lipe-lpcc package", LOG_WARNING_LEVEL
                )

    def _build_lustre_client(self):
        if ".tar.gz" in os.path.split(self._lustre_src)[-1:][0]:
            ret = self._run_cmd(
                ["tar", "xpf", self._lustre_src, "-C", self._update_dir],
                dry_run=self._dry_run,
            )[0]
            if not self._dry_run:
                for name in os.listdir(self._update_dir):
                    if (
                        os.path.isdir(os.path.join(self._update_dir, name))
                        and "lustre" in name
                    ):
                        lustre = name
                if ret != 0:
                    self._print_info(
                        "Unable to unpack lustre source file.", LOG_ERROR_LEVEL
                    )
            else:
                lustre = ""
        else:
            lustre = os.path.split(self._lustre_src)[-1:][0]
            if not self._dry_run:
                shutil.copytree(
                    self._lustre_src, os.path.join(self._update_dir, lustre)
                )
        cmds_to_execute = []
        self._print_info(
            "\nBuilding EXAScaler client software. This may take a while...",
            log_to_console=True,
        )

        rc, nproc = self._run_cmd(["nproc"])
        if rc != 0:
            self._print_info("Unable to get processor details", LOG_WARNING_LEVEL)
            nproc = "1"

        if self._linux_distribution_name == "ubuntu":
            packages_output_path = "/opt/ddn/exascaler/debs"
            if self._mofed_installed:
                if os.path.exists(
                    "/usr/src/ofa_kernel/x86_64/{0}".format(self._target_kernel)
                ):
                    mofed_path = "/usr/src/ofa_kernel/x86_64/{0}".format(
                        self._target_kernel
                    )
                elif os.path.exists(
                    "/usr/src/ofa_kernel/{0}".format(self._target_kernel)
                ):
                    mofed_path = "/usr/src/ofa_kernel/{0}".format(self._target_kernel)
                else:
                    mofed_path = "/usr/src/ofa_kernel/default"
            cmds_to_execute.append(["sh", "autogen.sh"])
            cmds_to_execute.append(
                [
                    "./configure",
                    "--with-linux=/usr/src/linux-headers-{0}".format(
                        self._target_kernel
                    ),
                    "--disable-server",
                    "--disable-tests",
                    "--with-o2ib=" + mofed_path
                    if self._mofed_installed
                    else ""
                    if not self._disable_o2ib
                    else "--with-o2ib=no",
                ]
            )

            cmds_to_execute.append(["make", "debs", "-j", nproc.strip()])
            # Remove lustre-tests since "--disable-tests" has no effect on debs creation
            cmds_to_execute.append(["rm", "-f", "debs/lustre-tests*.deb"])
            cmds_to_execute.append(["rm", "-f", "debs/lustre-iokit*.deb"])
            cmds_to_execute.append(["rm", "-f", "debs/lustre-source*.deb"])
            cmds_to_execute.append(["apt", "-y", "install", "./debs/lustre*.deb"])
            cmds_to_execute.append(["mkdir", "-p", packages_output_path])
            cmds_to_execute.append(["mv", "debs/lustre*.deb", packages_output_path])
        else:
            packages_output_path = "/opt/ddn/exascaler/rpms"
            if self._linux_distribution[1][0] == "7":
                self._run_cmd(
                    ["autoreconf", "--force", "--install"],
                    self._dry_run,
                    cwd=os.path.join(self._update_dir, lustre),
                )
            cmds_to_execute.append(["sh", "autogen.sh"])
            cmds_to_execute.append(
                [
                    "./configure",
                    "--disable-server",
                    "--disable-tests",
                    "--with-o2ib=yes"
                    if self._mofed_installed
                    else ""
                    if not self._disable_o2ib
                    else "--with-o2ib=no",
                ]
            )
            cmds_to_execute.append(["make", "rpms", "-j", nproc.strip()])
            cmds_to_execute.append(["rm", "-f", "*lustre-client-debug*.rpm"])
            cmds_to_execute.append(
                [
                    "yum",
                    "install",
                    "-y",
                    "kmod-lustre-client-*.rpm",
                    "lustre-client*.rpm",
                ]
            )
            cmds_to_execute.append(["mkdir", "-p", packages_output_path])
            cmds_to_execute.append(
                [
                    "mv",
                    "kmod-lustre-client-*.rpm",
                    "lustre-client*.rpm",
                    packages_output_path,
                ]
            )
        for cmd in cmds_to_execute:
            ret, _ = self._run_cmd(
                cmd, self._dry_run, cwd=os.path.join(self._update_dir, lustre)
            )
            if ret:
                self._clean_builddir = False
                self._print_info(
                    "Lustre build command failed {0} {1}. error {2}".format(
                        cmd, _, ret
                    ),
                    LOG_ERROR_LEVEL,
                )
        self._print_info(
            "EXAScaler client software packages are installed and placed in {0} folder".format(
                packages_output_path
            ),
            log_to_console=True,
        )

    def _install_lustre_client_dkms(self):
        cmds_to_execute = []
        self._print_info(
            "\nInstalling EXAScaler dkms client software. This may take a while...",
            log_to_console=True,
        )
        if self._linux_distribution_name == "ubuntu":
            cmds_to_execute.append(["apt", "update"])
            cmds_to_execute.append(
                [
                    "apt",
                    "install",
                    "-o DPkg::Options::='--force-confnew'",
                    "-y",
                    "lustre-client-utils",
                    "lustre-client-modules-dkms",
                    "lustre-dev",
                    "lipe-lpcc",
                    "fscrypt",
                ]
            )
        else:
            if self._linux_distribution[1][0] in ("8", "9"):
                cmds_to_execute.append(
                    [
                        "yum install -y lustre-client "
                        "lustre-client-dkms "
                        "lustre-client-devel "
                        "fscrypt lipe-lpcc"
                    ]
                )
            else:
                cmds_to_execute.append(
                    [
                        "yum install -y lustre-client "
                        "lustre-client-dkms lustre-client-devel "
                        "lipe-lpcc"
                    ]
                )
        for cmd in cmds_to_execute:
            ret, _ = self._run_cmd(
                cmd,
                self._dry_run,
                env=dict(os.environ, DEBIAN_FRONTEND="noninteractive"),
            )
            if ret:
                self._clean_builddir = False
                self._print_info(
                    "Lustre client installation command failed {0} {1}. error {2}".format(
                        cmd, _, ret
                    ),
                    LOG_ERROR_LEVEL,
                )
        self._print_info(
            "EXAScaler dkms client software packages are installed from {}".format(
                self._emf_ip
            ),
            log_to_console=True,
        )

    def _setup_install_lustre_client_dkms(self):
        if self._linux_distribution_name == "ubuntu":
            output_file = "/etc/apt/sources.list.d/exascaler-client.list"
            ubuntu_version = "".join(
                ch for ch in "".join(self._linux_distribution[:-1]) if ch.isalnum()
            ).lower()
            repo_content = "deb [trusted=yes] http://{}:{}/client/{} ./".format(
                self._emf_ip, "7080", ubuntu_version
            )
        else:
            output_file = "/etc/yum.repos.d/exascaler-client.repo"
            centos_version = "el{}{}".format(
                self._linux_distribution[1][0], self._linux_distribution[1][2]
            )
            repo_content = """
[exa-client]
name=exa client repo
baseurl=http://{}:{}/client/{}/
gpgcheck=0
            """.format(
                self._emf_ip, "7080", centos_version
            )
        if self._dry_run:
            print("$ echo", repo_content, ">", output_file)
        else:
            with open(output_file, "w") as f:
                f.write(repo_content)

    def get_lustre_debs_installed(self):
        # Check for lustre packages
        rc, out = self._run_cmd(["dpkg", "-l", "'lustre*'"])
        packages = []
        if rc == 0:
            pkgs = re.findall(r"^(\w+)\s+(lustre[\w\.-]+).*$", out, re.M)
            for state, pkg in pkgs:
                if state == "ii" or state == "ri" or state == "iU":
                    packages.append(pkg)
        # Check for lipe packages
        rc, out = self._run_cmd(["dpkg", "-l", "'lipe*'"])
        if rc == 0:
            pkgs = re.findall(r"^(\w+)\s+(lipe[\w\.-]+).*$", out, re.M)
            for state, pkg in pkgs:
                if state == "ii" or state == "ri" or state == "iU":
                    packages.append(pkg)

        return packages

    def get_lustre_rpms_installed(self):
        rc, out = self._run_cmd(
            ["rpm", "-qa", "'lustre*'", "'kmod-lustre*'", "'lipe*'"]
        )
        packages = []
        if rc == 0:
            packages = out.splitlines()
        return packages

    def get_kernel_headers_rpms_available_version(self):
        rc, out = self._run_cmd(["yum", "list", '"kernel-headers"'])
        packages_version = []
        if rc == 0:
            read_line = False
            for p in out.splitlines():
                if read_line:
                    packages_version.append(p.split()[1])
                if p == "Available Packages":
                    read_line = True
        rc, out = self._run_cmd(["rpm", "-q", "kernel-headers"])
        if rc == 0:
            packages_version.extend(out.splitlines())
        return packages_version

    def check_rhel_kernel_headers(self):
        regex_kernel = r"[0-9]+\.[0-9]+\.[0-9]+-[0-9]+\.[0-9]+"
        # Keep X.Y.Z-V.W string (eg 4.18.0-240.22)
        running_kernel = re.search(regex_kernel, str(self._target_kernel))
        if not running_kernel:
            # Keep X.Y.Z-V string (eg 3.10.0-1127)
            regex_kernel = r"[0-9]+\.[0-9]+\.[0-9]+-[0-9]+"
            running_kernel = re.search(regex_kernel, str(self._target_kernel))
            if not running_kernel:
                self._print_info(
                    "\nCan't extract kernel version from {}".format(
                        self._target_kernel
                    ),
                    LOG_ERROR_LEVEL,
                )
            else:
                running_kernel = running_kernel.group(0)
        else:
            running_kernel = running_kernel.group(0)
        headers_found = False
        for install_headers in self.get_kernel_headers_rpms_available_version():
            found = re.search(regex_kernel, str(install_headers))
            if found:
                if running_kernel == found.group(0):
                    headers_found = True

        if not headers_found:
            self._print_info(
                "\nHeaders can't be found for running kernel {0}.\nFound headers available for {1}. Please update your kernel or install manually your running kernel headers".format(
                    self._target_kernel,
                    "".join(self.get_kernel_headers_rpms_available_version()),
                ),
                LOG_ERROR_LEVEL,
            )

    def get_installed_pkg_version(self, pkg):
        _, out = self._run_cmd(
            ["dpkg-query", "--showformat='${Version}'", "--show", pkg]
        )
        return out

    def is_lustre_installed(self, print_info=False):
        """Check lustre packages are installed."""

        if self._linux_distribution_name == "ubuntu":
            packages = self.get_lustre_debs_installed()
        else:
            packages = self.get_lustre_rpms_installed()
        if packages:
            # Check if lustre has been compiled against the current kernel
            try:
                ret, out = self._run_cmd(["modinfo", "lustre"], dry_run=self._dry_run)
                vermagic = re.search("vermagic.*", out).group(0).split()[1]
                ret, out = self._run_cmd(["uname", "-a"], dry_run=self._dry_run)
                if not vermagic in out and print_info:
                    self._print_info(
                        "WARNING: EXAScaler module doesn't match current kernel",
                        LOG_WARNING_LEVEL,
                    )
            except Exception as e:
                self._print_info(e, LOG_INFO_LEVEL)
                self._print_info("Can't compare modinfo/uname", LOG_INFO_LEVEL)
            if self._linux_distribution_name == "ubuntu":
                version = self.get_installed_pkg_version(packages[0])
                if print_info:
                    self._print_info(
                        "Found installed EXAScaler client software packages version {}:\n".format(
                            version
                        ),
                        log_to_console=True,
                    )
            else:
                if print_info:
                    self._print_info(
                        "Found installed EXAScaler client software packages:\n",
                        log_to_console=True,
                    )
            for package in packages:
                if print_info:
                    self._print_info(package, log_to_console=True)
            return True
        else:
            if print_info:
                self._print_info(
                    "EXAScaler client software packages are not installed\n",
                    log_to_console=True,
                )
            return False

    def _stop_lustre(self):
        """Stopping lustre on node."""

        self._print_info("Stopping lustre on node.")

        if not self._dry_run:
            (ret, _) = self._run_cmd(["lustre_rmmod"], dry_run=self._dry_run)
            if ret != 0:
                (ret, _) = self._run_cmd(
                    ["service", "lnet", "stop"], dry_run=self._dry_run
                )
                if ret != 0:
                    (ret, _) = self._run_cmd(
                        ["lctl", "network", "down"], dry_run=self._dry_run
                    )
                    if ret != 0:
                        self._print_info("Can not stop lustre.", LOG_INFO_LEVEL)
                (ret, _) = self._run_cmd(["lustre_rmmod"], dry_run=self._dry_run)
                if ret != 0:
                    self._print_info("Can not stop lustre.", LOG_INFO_LEVEL)

        self._print_info("Lustre was stopped on node.")

    def _is_lustre_mounted(self, unmount=False):
        mounted = False
        mounts = []
        rc, output = self._run_cmd(["findmnt", "-t", "lustre", "-P", "-o", "TARGET"])
        if rc == 0:
            mounts = re.findall(r'TARGET="(.+)"', output)
            if not unmount:
                self._print_info(
                    "\nFound mounted lustre file system(s): {0}".format(mounts),
                    log_to_console=True,
                )
            mounted = True
        if unmount:
            for mount in mounts:
                rc, _ = self._run_cmd(["umount", "-lf", mount], dry_run=self._dry_run)
                if rc != 0:
                    self._print_info(
                        "Failed to unmount lustre from {0}".format(mount),
                        LOG_ERROR_LEVEL,
                    )
                    mounted = False
        return mounted

    def _remove_tmp_packages(self, *args):
        """Removing temporary packages."""

        self._print_info("Removing temporary packages")
        if self._linux_distribution_name == "ubuntu":
            packages_to_remove = ["lustre-source"]
        else:
            packages_to_remove = []
        packages_to_processing = []
        packages_to_remove.extend(args)

        for package_to_remove in packages_to_remove:
            if (
                self._linux_distribution_name == "ubuntu"
                and self._is_deb_installed(package_to_remove)
            ) or (
                self._linux_distribution_name != "ubuntu"
                and self._is_rpm_installed(package_to_remove)
            ):
                packages_to_processing.append(package_to_remove)

        self._print_info(
            "Packages to remove: {0}.".format(",".join(packages_to_processing))
        )

        if not self._dry_run:
            if self._linux_distribution_name == "ubuntu":
                self._run_cmd(
                    ["dpkg", "--remove"] + packages_to_processing, self._dry_run
                )
            else:
                self._run_cmd(
                    ["yum", "remove", "-y"] + packages_to_processing, self._dry_run
                )

        self._print_info("Temporary packages were removed.")

    def _get_attr(self, attr_path):
        rc, out = self._run_cmd(["sysctl", attr_path])
        if rc != 0 or out is None:
            self._print_info("Unable to get {0}".format(attr_path))
            return None

        return out.split(" = ")[1]

    def _build_arp_info(self, nics):
        arp_info = {}
        all_prefix = "net.ipv4.conf.all."
        nic_prefix = "net.ipv4.conf."

        for attr, value in ARP_INFO.items():
            attr_path = all_prefix + attr
            if self._get_attr(attr_path) is not None:
                arp_info[attr_path] = value

        for nic in nics:
            if ":" not in nic:
                for attr, value in NICS_ARP_INFO.items():
                    attr_path = nic_prefix + nic + "." + attr
                    if self._get_attr(attr_path) is not None:
                        arp_info[attr_path] = value

        return arp_info

    def _set_arp(self, arp):
        # Write conf
        if not self._dry_run:
            with open("/etc/sysctl.d/99-exascaler.conf", "w+") as f:
                for attr_path, value in arp.items():
                    f.write("{0}={1}\n".format(attr_path, value))
        else:
            for attr_path, value in arp.items():
                print(
                    "echo '{0}={1}' >> /etc/sysctl.d/99-exascaler.conf".format(
                        attr_path, value
                    )
                )
        # Apply conf
        self._run_cmd(["sysctl", "--system"], self._dry_run)

    def _add_routes(self, nics):
        rc, out = self._run_cmd(["ip", "route", "show", "table", "all"], False)
        for rt in out.split("\n"):
            if "table" not in rt:
                continue
            table_name = rt.split("table")[1].strip().split()[0]
            if table_name in nics:
                self._run_cmd(
                    ["ip", "route", "flush", "table", table_name], self._dry_run
                )

        with open("/etc/iproute2/rt_tables", "r") as f:
            lines = f.readlines()
        max_table_num = 0
        if sys.version_info[0] < 3:
            local_intf_list = list(nics)
        else:
            local_intf_list = nics.copy()

        for line in lines:
            found = False
            if len(line.strip()) > 0 and line.strip()[0] == "#":
                continue

            split = re.split("\t+| ", line)
            try:
                table_num = int(split[0].strip())
            except:
                continue
            nic_raw = ""
            if len(split) > 1:
                nic_raw = split[1].strip()
            if max_table_num < table_num:
                max_table_num = table_num

            for nic in nics:
                if nic == nic_raw:
                    local_intf_list.remove(nic)
                    break

        for nic in local_intf_list:
            max_table_num += 1
            if not self._dry_run:
                with open("/etc/iproute2/rt_tables", "a") as f:
                    f.write("\n" + str(max_table_num) + " " + nic)
            else:
                print(
                    "echo '"
                    + str(max_table_num)
                    + " "
                    + nic
                    + "' >> /etc/iproute2/rt_tables"
                )
        try:
            import netifaces
            from netaddr import IPNetwork
        except ImportError as e:
            self._prepare_python_env()
            import netifaces
            from netaddr import IPNetwork

        for nic in nics:
            addr = netifaces.ifaddresses(nic)[netifaces.AF_INET][0]["addr"]
            netmask = netifaces.ifaddresses(nic)[netifaces.AF_INET][0]["netmask"]
            cidr = str(IPNetwork(addr + "/" + netmask).cidr)

            cmd = [
                "ip",
                "route",
                "add",
                cidr,
                "dev",
                nic,
                "proto",
                "kernel",
                "scope",
                "link",
                "src",
                addr,
                "table",
                nic,
            ]
            self._run_cmd(cmd, self._dry_run)
            cmd = ["ip", "rule", "del", "from", addr, "table", nic]
            self._run_cmd(cmd, self._dry_run)
            cmd = ["ip", "rule", "add", "from", addr, "table", nic]
            self._run_cmd(cmd, self._dry_run)

        self._run_cmd(["ip", "route", "flush", "cache"], self._dry_run)

    def _flush_neigh(self, nics):
        for nic in nics:
            cmd = ["ip", "neigh", "flush", "dev", nic]
            self._run_cmd(cmd, self._dry_run)

    def _tune_eth_nics(self, nics):
        # Convert aliases to actual nic
        try:
            nics_without_aliases = list(
                map(lambda nic: re.sub(r":[0-9]+", "", nics), nics)
            )
        except Exception as err:
            self._print_info(err, LOG_DEBUG_LEVEL)
            self._print_info(
                "Can't convert aliases in nic list, ethernet tuning skipped",
                LOG_DEBUG_LEVEL,
            )
            return False

        # Applies ethernet tunings for each ethernet nic in nics
        # return True if success
        no_error = True

        # Check that lshw command is available
        # We use this command to retrieve nics informations
        cmd = ["command", "-v", "lshw"]
        rc, out = self._run_cmd(cmd)
        if rc != 0:
            self._print_info(
                "lshw isn't available, ethernet tuning skipped", LOG_INFO_LEVEL
            )
            return False

        # Retrieve information
        cmd = ["lshw", "-class", "network", "-xml"]
        rc, out = self._run_cmd(cmd)
        if rc != 0:
            self._print_info("lshw failed, ethernet tuning skipped", LOG_INFO_LEVEL)
            return False
        try:
            # use xml, json is buggy for old version of lshw
            out_xml = ET.fromstring(out)
        except Exception as err:
            self._print_info(err, LOG_INFO_LEVEL)
            self._print_info(
                "Can't read lshw xml output, ethernet tuning skipped", LOG_INFO_LEVEL
            )
            return False

        # Create a list containing all ethernet nics
        nics_with_ethernet = []
        mlx_nics = []

        # TODO: Simplify this loop
        try:
            for nic in nics_without_aliases:
                nic_found = False
                nic_has_ethernet = False
                for interface in out_xml:
                    for subsection in interface:
                        if subsection.tag == "logicalname" and subsection.text == nic:
                            nic_found = True
                            # Search if nic has ethernet
                            for subsection2 in interface:
                                if subsection2.tag == "capabilities":
                                    for subsection3 in subsection2:
                                        for element in subsection3.attrib:
                                            if (
                                                "ethernet"
                                                in subsection3.attrib[element]
                                            ):
                                                nics_with_ethernet.append(nic)
                                                nic_has_ethernet = True
                                                break
                                    if nic_has_ethernet:
                                        break
                                if nic_has_ethernet:
                                    break
                            # Search if is mlx
                            for subsection2 in interface:
                                if (
                                    subsection2.tag == "vendor"
                                    and "Mellanox" in subsection2.text
                                ):
                                    mlx_nics.append(nic)
                                    break
                            break
                    if nic_found:
                        break
        except Exception as err:
            self._print_info(err, LOG_INFO_LEVEL)
            self._print_info("Error parsing lshw xml output", LOG_INFO_LEVEL)
            return False

        # No ethernet, nothing to do
        if len(nics_with_ethernet) <= 0:
            self._print_info(
                "No ethernet interface found, skip eth tuning", LOG_INFO_LEVEL
            )
        else:
            # If we didn't use -k option and we answer yes to "Apply Ethernet tuning" => tune
            apply_eth_tuning = False
            if not self._skip_eth_tuning:
                if yes_no_query("\nApply Ethernet tunings", "yes", self._yes):
                    apply_eth_tuning = True
                else:
                    # Update skip_eth_tuning to reflect user choice
                    self._skip_eth_tuning = True

            if apply_eth_tuning:
                # Check that ethtool is installed
                cmd = ["command", "-v", "ethtool"]
                rc, out = self._run_cmd(cmd)
                if rc != 0:
                    self._print_info(
                        "ethtool isn't installed, ethernet tuning skipped",
                        LOG_INFO_LEVEL,
                    )
                    return False

                # Ethernet tuning can take time, display ETA to the user
                self._print_info(
                    "Applying Ethernet tuning (ETA: <"
                    + str(len(nics_with_ethernet))
                    + " minutes)",
                    log_to_console=True,
                )

                # For each eth nic we try to:
                #  - increase ring parameters
                #  - increase channel parameters
                #  - enable large receive offload
                #  - increase transmit queue length
                # If nic is mlx we also:
                #  - enable relax ordering (reboot is necessary)
                for nic in nics_with_ethernet:
                    # Try to tune ring parameters
                    cmd = ["ethtool", "-g", str(nic)]
                    rc, out = self._run_cmd(cmd)
                    if rc != 0:
                        # ring parameter not available for this nic
                        self._print_info(
                            "No ring parameters for interface " + str(nic),
                            LOG_INFO_LEVEL,
                        )
                    else:
                        RX = 8192
                        TX = 8192
                        # Find maximum ring values
                        # Latest versions of ethtool have a json output
                        # but most version circulating don't
                        try:
                            maximum_presets = re.search(
                                r".*Pre-set maximums\s*:\s*(.*)$",
                                out,
                                flags=re.IGNORECASE | re.DOTALL,
                            )
                            # Find maximum RX, re.search stop at first match
                            # https://docs.python.org/3/library/re.html#re.Pattern.search
                            rx = int(
                                re.search(
                                    r"[0-9]+",
                                    re.search(
                                        r"RX:.*",
                                        maximum_presets.group(1),
                                        flags=re.IGNORECASE,
                                    ).group(0),
                                ).group(0)
                            )
                            if rx < RX:
                                RX = rx
                            tx = int(
                                re.search(
                                    r"[0-9]+",
                                    re.search(
                                        r"TX:.*",
                                        maximum_presets.group(1),
                                        flags=re.IGNORECASE,
                                    ).group(0),
                                ).group(0)
                            )
                            if tx < TX:
                                TX = tx
                            # Apply new values

                            cmd = [
                                "ethtool",
                                "-G",
                                str(nic),
                                "rx",
                                str(RX),
                                "tx",
                                str(TX),
                            ]
                            rc, out = self._run_cmd(cmd, self._dry_run)
                            if rc != 0 and rc != 80:  # 80 means unmodified
                                raise Exception(
                                    "Can't tune ring parameters for interface "
                                    + str(nic)
                                    + " (ethtool error)"
                                )

                        except Exception as err:
                            self._print_info(err, LOG_INFO_LEVEL)
                            self._print_info(
                                "Can't tune ring parameters for interface "
                                + str(nic)
                                + " (parsing error)",
                                LOG_INFO_LEVEL,
                            )
                            no_error = False

                    # Try to tune channel parameters
                    cmd = ["ethtool", "-l", str(nic)]
                    rc, out = self._run_cmd(cmd)
                    if rc != 0:
                        self._print_info(
                            "No channel parameters for interface " + str(nic),
                            LOG_INFO_LEVEL,
                        )
                    else:
                        COMBINED = 32
                        try:
                            maximum_presets = re.search(
                                r".*Pre-set maximums\s*:\s*(.*)$",
                                out,
                                flags=re.IGNORECASE | re.DOTALL,
                            )
                            combined = int(
                                re.search(
                                    r"[0-9]+",
                                    re.search(
                                        r"Combined:.*",
                                        maximum_presets.group(1),
                                        flags=re.IGNORECASE,
                                    ).group(0),
                                ).group(0)
                            )
                            if combined < COMBINED:
                                COMBINED = combined
                            # Apply new values

                            cmd = ["ethtool", "-L", str(nic), "combined", str(COMBINED)]
                            rc, out = self._run_cmd(cmd, self._dry_run)
                            if rc != 0 and rc != 80:  # 80 means unmodified
                                raise Exception(
                                    "Can't tune channel parameters for interface "
                                    + str(nic)
                                    + " (ethtool error)"
                                )

                        except Exception as err:
                            self._print_info(err, LOG_INFO_LEVEL)
                            self._print_info(
                                "Can't tune channel parameters for interface "
                                + str(nic)
                                + " (parsing error)",
                                LOG_INFO_LEVEL,
                            )
                            no_error = False

                    # Try to enable large receive
                    cmd = ["ethtool", "-k", str(nic)]
                    rc, out = self._run_cmd(cmd)
                    if rc != 0:
                        self._print_info(
                            "No lro parameters for interface " + str(nic),
                            LOG_INFO_LEVEL,
                        )
                    else:
                        COMBINED = 32
                        try:
                            lro_exit = re.search(
                                r"large-receive-offload:.*", out, flags=re.IGNORECASE
                            )
                            if lro_exit != None:
                                if "[fixed]" not in lro_exit.group(0):
                                    # Apply new values
                                    cmd = ["ethtool", "-K", str(nic), "lro", "on"]
                                    rc, out = self._run_cmd(cmd, self._dry_run)
                                    if rc != 0 and rc != 80:  # 80 means unmodified
                                        raise Exception(
                                            "Can't enable large receive offload for interface "
                                            + str(nic)
                                            + " (ethtool error)"
                                        )
                        except Exception as err:
                            self._print_info(err, LOG_INFO_LEVEL)
                            self._print_info(
                                "Can't enable large receive offload for interface "
                                + str(nic)
                                + " (parsing error)",
                                LOG_INFO_LEVEL,
                            )
                            no_error = False

                    # Try to increase transmit queue length
                    cmd = ["ip", "link", "set", str(nic), "txqueuelen", "20000"]
                    rc, out = self._run_cmd(cmd, self._dry_run)
                    if rc != 0:
                        self._print_info(
                            "Can't increase transmit queue lenght for interface "
                            + str(nic),
                            LOG_INFO_LEVEL,
                        )
                        no_error = False

        # Try to enable relax ordering (mlx only)
        if len(mlx_nics) <= 0:
            self._print_info(
                "No Mellanox interface found, skip relax ordering tuning",
                LOG_INFO_LEVEL,
            )
            return no_error

        # Skip relax ordering tuning if we used -j or answered no to Apply Relax ordering
        apply_ro_tuning = False
        if not self._skip_ro_tuning:
            if yes_no_query("\nApply Relax Ordering (mlx)", "yes", self._yes):
                apply_ro_tuning = True
            else:
                # Update skip_ro_tuning to reflect user choice
                self._skip_ro_tuning = True

        if not apply_ro_tuning:
            return no_error

        # Enable mst
        cmd = ["mst", "start"]
        rc, out = self._run_cmd(cmd)
        if rc != 0:
            self._print_info(
                "Can't modify relax ordering (mst start failed)", LOG_INFO_LEVEL
            )
            return False

        # Search ifs names
        cmd = ["mst", "status", "-v"]
        rc, mst_status = self._run_cmd(cmd)
        if rc != 0:
            self._print_info(
                "Can't modify relax ordering (mst status failed)", LOG_INFO_LEVEL
            )
            return False

        relax_ordering_set_on_at_least_one_if = False
        # For each mlx eth nic, enable relax ordering
        for nic in mlx_nics:
            try:
                # Search line in mst status
                nic_line = re.search(r".*" + nic + r".*", mst_status)
                if nic_line == None:
                    raise Exception("Can't find interface in mst status")
                # Search device
                device = re.search(r"/dev/[^ ]+", nic_line.group(0))
                if device == None:
                    raise Exception("Can't find device in mst status")
                # Query the relax ordering value
                cmd = ["mlxconfig", "-d", str(device.group(0)), "q"]
                rc, out = self._run_cmd(cmd)
                if rc != 0:
                    raise Exception("Can't parse current relax ordering value")
                current_ordering = re.search(r".*PCI_WR_ORDERING.*", out)
                relax_ordering = re.search(
                    r"force_relax\(1\)", current_ordering.group(0)
                )
                # If relax ordering isn't set:
                if relax_ordering == None:
                    cmd = [
                        "mlxconfig",
                        "-y",
                        "-d",
                        str(device.group(0)),
                        "s",
                        "PCI_WR_ORDERING=1",
                    ]
                    rc, out = self._run_cmd(cmd, self._dry_run)
                    if rc != 0:
                        raise Exception("PCI_WR_ORDERING=1 has failed")
                    else:
                        relax_ordering_set_on_at_least_one_if = True
                else:
                    self._print_info(
                        "Relax ordering already set for " + str(nic), LOG_INFO_LEVEL
                    )

            except Exception as err:
                self._print_info(err, LOG_INFO_LEVEL)
                self._print_info(
                    "Can't modify relax ordering for " + str(nic), LOG_INFO_LEVEL
                )
                no_error = False

        if relax_ordering_set_on_at_least_one_if:
            self._print_info(
                "Relax ordering has been modified, please reboot",
                LOG_INFO_LEVEL,
                log_to_console=True,
            )
        return no_error

    def _configure_routing(self, nics):
        arp_info = self._build_arp_info(nics)
        self._set_arp(arp_info)
        self._add_routes(nics)
        self._flush_neigh(nics)

    def _configure_lnet_conf(self):
        cmd = ["modprobe", "lnet"]
        self._run_cmd(cmd, self._dry_run)
        cmd = ["lnetctl", "lnet", "configure", "--all"]
        self._run_cmd(cmd, self._dry_run)
        cmd = ["lnetctl", "export", "--backup"]
        rc, out = self._run_cmd(cmd, self._dry_run)
        if rc == 0 and not self._dry_run:
            with open("/etc/lnet.conf", "w") as f:
                f.write(out)
        cmd = ["lnetctl", "lnet", "unconfigure"]
        self._run_cmd(cmd, self._dry_run)
        cmd = ["lustre_rmmod"]
        self._run_cmd(cmd, self._dry_run)

    def _get_lustre_conf(self):
        lustre_conf = collections.defaultdict(dict)
        with open("/etc/modprobe.d/lustre.conf") as f:
            for line in f.readlines():
                if line.startswith("options"):
                    module_name = line.split()[1]
                    if module_name in lustre_conf:
                        module_params = lustre_conf[module_name]
                    else:
                        module_params = {}
                    template = re.compile(r"[^ ]+=(\".*\"|[^ ]*)")
                    module_options = re.finditer(template, line)
                    for module_option in module_options:
                        option = module_option.group(0).strip().split("=")
                        module_params[option[0]] = option[1]
                    lustre_conf[module_name] = module_params
        return lustre_conf

    def _set_lustre_conf(self, lustre_conf):
        if not self._dry_run:
            f = open("/etc/modprobe.d/lustre.conf", "w")
            # Add header
            f.write(
                """# This file has been generated by exa-client-deploy
#
# Do not edit unless exa-client-deploy service is stopped & disabled
# e.g: 'systemctl status exa-client-deploy'
#

"""
            )
        for module, module_options in lustre_conf.items():
            for module_option, value in module_options.items():
                if not self._dry_run:
                    f.write(
                        "options " + module + " " + module_option + "=" + value + "\n"
                    )
                else:
                    print(
                        "echo 'options "
                        + module
                        + " "
                        + module_option
                        + "="
                        + value
                        + "' >> /etc/modprobe.d/lustre.conf"
                    )
        if not self._dry_run:
            f.close()

    def _is_intf_configured(self, intf):
        try:
            import netifaces
        except ImportError as e:
            self._prepare_python_env()
            import netifaces

        wait_time = 0
        while wait_time < 60:
            addr = netifaces.ifaddresses(intf)
            if netifaces.AF_INET in addr:
                return True
            else:
                time.sleep(5)
                wait_time += 5

        return False

    def _configure_persistent(self):
        # Check systemd is available
        try:
            cmd = ["command", "-v", "systemctl"]
            rc, out = self._run_cmd(cmd)
            if rc != 0:
                self._print_info(
                    "systemctl isn't available, persistency skipped", LOG_INFO_LEVEL
                )
                return False
        except Exception as e:
            self._print_info("Can't use command\n".format(e), LOG_INFO_LEVEL)
            return False

        # Create /opt/ddn/exascaler/systemd/
        try:
            if not os.path.exists("/opt/ddn/exascaler/systemd"):
                self._print_info(
                    "Create a directory for systemd service in /opt/ddn/exascaler/systemd",
                    LOG_INFO_LEVEL,
                    log_to_console=self._dry_run,
                )
                if not self._dry_run:
                    os.makedirs("/opt/ddn/exascaler/systemd")
        except Exception as e:
            self._print_info(
                "Can't create /opt/ddn/exascaler/systemd\n{}".format(e), LOG_INFO_LEVEL
            )
            return False

        # Copy this script to /opt/ddn/exascaler
        src = os.path.join(self._script_directory, __file__)
        dst = "/opt/ddn/exascaler/exa_client_deploy"
        try:
            self._print_info(
                "COPY {} to {}".format(src, dst),
                LOG_INFO_LEVEL,
                log_to_console=self._dry_run,
            )
            if not self._dry_run:
                shutil.copy(src, dst)
        except Exception as e:
            self._print_info("Can't copy {} to {}\n{}".format(src, dst, e))
            return False

        # Set +x for /opt/ddn/exascaler/exa_client_deploy.py
        try:
            cmd = ["chmod", "+x", dst]
            rc, out = self._run_cmd(cmd, self._dry_run)
            if rc != 0:
                self._print_info("chmod +x {} failed".format(dst), LOG_INFO_LEVEL)
                raise
        except Exception as e:
            # Warning if chmod fails
            self._print_info(
                "Failed to add execution permission to {}\nexa-client-deploy service may malfunction\n".format(
                    dst
                ),
                LOG_WARNING_LEVEL,
            )

        # Add options
        tunings = []
        if self._skip_eth_tuning:
            tunings.append("--skip-eth-tuning")
        if self._skip_ro_tuning:
            tunings.append("--skip-ro-tuning")
        if self._cpu_npartitions != None:
            tunings.append("-n {}".format(self._cpu_npartitions))

        # Create systemd file
        systemdfile = """
[Unit]
Description=Configure EXA Interfaces
After=network.target network-online.target openibd.service
Before=lnet.service

[Service]
Type=oneshot
RemainAfterExit=true
ExecStart=/opt/ddn/exascaler/exa_client_deploy -c -l "{}" --yes {}

[Install]
WantedBy=default.target
        """.format(
            ",".join(self._lnets), " ".join(tunings)
        )
        self._print_info(systemdfile, LOG_INFO_LEVEL, log_to_console=self._dry_run)

        # Copy systemd file to /opt/ddn/exascaler/systemd/
        try:
            self._print_info(
                "Write /opt/ddn/exascaler/systemd/exa_client_deploy.service",
                LOG_INFO_LEVEL,
                log_to_console=self._dry_run,
            )
            if not self._dry_run:
                exa_service_file = open(
                    "/opt/ddn/exascaler/systemd/exa-client-deploy.service", "w"
                )
                exa_service_file.write(systemdfile)
                exa_service_file.close()
        except Exception as e:
            self._print_info(
                "Can't write /opt/ddn/exascaler/systemd/exa-client-deploy.service",
                LOG_INFO_LEVEL,
            )
            return False

        # Enable systemd service
        try:
            # Check systemd is available
            cmd = [
                "systemctl",
                "enable",
                "/opt/ddn/exascaler/systemd/exa-client-deploy.service",
            ]
            rc, out = self._run_cmd(cmd, self._dry_run)
            if rc != 0 and not self._dry_run:
                raise
        except Exception as e:
            self._print_info(
                "Can't enable service /opt/ddn/exascaler/systemd/exa-client-deploy.service\n{}".format(
                    e
                ),
                LOG_INFO_LEVEL,
            )
            return False

        self._print_info(
            "Persistency enabled (see /opt/ddn/exascaler/systemd/exa-client-deploy.service)\n"
            "$ systemctl restart exa-client-deploy # Restart\n"
            "$ systemctl status  exa-client-deploy # Status\n"
            "$ systemctl disable exa-client-deploy # Disable\n",
            LOG_INFO_LEVEL,
            log_to_console=True,
        )
        return True

    def _configure_lnet(self):
        for nic in self._nics:
            if not self._is_intf_configured(nic):
                self._print_info(
                    "\nNetwork interface {0} doesn't have IP address configured. Aborting...".format(
                        nic
                    ),
                    LOG_ERROR_LEVEL,
                )
        self._stop_lustre()
        # Configure MR routing
        if len(self._nics) > 1:
            self._configure_routing(self._nics)

        # Tune ethernet nics
        if not self._tune_eth_nics(self._nics):
            self._print_info(
                "Some Ethernet tunings have failed, please see A3I documentation",
                LOG_WARNING_LEVEL,
            )

        # Configure lustre.conf
        lustre_conf = collections.defaultdict(dict)
        if os.path.exists("/etc/modprobe.d/lustre.conf"):
            lustre_conf = self._get_lustre_conf()
        lustre_conf["lnet"]["networks"] = '"' + (",").join(self._lnets) + '"'
        if self._cpu_npartitions:
            lustre_conf["libcfs"]["cpu_npartitions"] = str(self._cpu_npartitions)
            lustre_conf["libcfs"][
                "cpu_pattern"
            ] = ""  # cpu_npartitions will only work if cpu_pattern is set to an empty string (LU-9905)
        if not "lnet_transaction_timeout" in lustre_conf["lnet"]:
            lustre_conf["lnet"]["lnet_transaction_timeout"] = "100"
        if not "lnet_retry_count" in lustre_conf["lnet"]:
            lustre_conf["lnet"]["lnet_retry_count"] = "2"

        if not "ko2iblnd" in lustre_conf:
            lustre_conf["ko2iblnd"]["peer_credits"] = "32"
            lustre_conf["ko2iblnd"]["peer_credits_hiw"] = "16"
            lustre_conf["ko2iblnd"]["concurrent_sends"] = "64"
        else:
            if not "peer_credits" in lustre_conf["ko2iblnd"]:
                lustre_conf["ko2iblnd"]["peer_credits"] = "32"
            if not "peer_credits_hiw" in lustre_conf["ko2iblnd"]:
                lustre_conf["ko2iblnd"]["peer_credits_hiw"] = "16"
            if not "concurrent_sends" in lustre_conf["ko2iblnd"]:
                lustre_conf["ko2iblnd"]["concurrent_sends"] = "64"

        if not "ksocklnd" in lustre_conf:
            lustre_conf["ksocklnd"]["conns_per_peer"] = "0"
        elif not "conns_per_peer" in lustre_conf["ksocklnd"]:
            lustre_conf["ksocklnd"]["conns_per_peer"] = "0"

        self._set_lustre_conf(lustre_conf)
        self._configure_lnet_conf()
        self._print_info(
            "\nEXAScaler client software is configured\n", log_to_console=True
        )

    def _get_default_lnet(self):
        intf_list = []
        rc, out = self._run_cmd(["ibdev2netdev"])
        if rc == 0:
            out = out.splitlines()
            template = re.compile(r"^mlx.*\sport\s1\s==>\s(?P<interface>\S+)\s\(Up\).*")
            for line in out:
                match = re.match(template, line)
                if match:
                    intf_list.append(match.group("interface"))
        if not intf_list:
            self._print_info("\nNo infiniband interface is up", LOG_INFO_LEVEL)
            return None

        return "o2ib(" + ",".join([str(intf) for intf in intf_list]) + ")"

    def _bootstrap_prompt(self):
        """Bootstrap."""

        self._print_info(
            "\nDDN EXAScaler client software installation tool: "
            "Version {0}".format(VERSION),
            LOG_INFO_LEVEL,
            log_to_console=True,
        )
        self._print_info("Select an option:", log_to_console=True)
        valid_choices = ("1", "2", "3", "4", "5", "6")

        def _choise():
            return input(
                "\n1) Check if DDN EXAScaler client software is installed\n"
                "2) Install DDN EXAScaler client software\n"
                "3) Configure DDN EXAScaler client software\n"
                "4) Remove DDN EXAScaler client software\n"
                "5) List DDN EXAScaler mount commands\n"
                "6) Exit\n"
            )

        choise = _choise()
        while choise not in valid_choices:
            self._print_info("Unsupported choice specified.", LOG_ERROR_LEVEL)
            choise = _choise()
        return choise

    def _apply_choise(self, choise):
        if choise == CHECK:
            self._make_upd_dir()
            self._print_info(
                "Checking if DDN EXAScaler client software packages are installed.",
                LOG_INFO_LEVEL,
            )
            return self.is_lustre_installed(True)
        if choise == INSTALL:
            if self._linux_distribution_name == "ubuntu":
                self._dump_debs_list()
            self._remove_tmp_packages()
            self._prepare_build_env()
            if self._dkms:
                self._setup_install_lustre_client_dkms()
                self._install_lustre_client_dkms()
            else:
                self._build_lustre_client()
                self._install_fscrypt()
                self._install_lipe()

            if not self._configure:
                self._print_info(
                    "Use option 3 to configure EXAScaler client software before loading lustre module\n",
                    log_to_console=True,
                )
            return True
        if choise == CONFIGURE:
            self._configure_lnet()
            if not self._skip_persistent:
                if not self._configure_persistent():
                    self._print_info("Setup persistency has failed", LOG_WARNING_LEVEL)

            return True
        if choise == REMOVE:
            self._stop_lustre()
            self._print_info("Removing lustre packages...", LOG_INFO_LEVEL)
            if self._linux_distribution_name == "ubuntu":
                self._dump_debs_list()
                self._remove_tmp_packages(*self.get_lustre_debs_installed())
            else:
                self._remove_tmp_packages(*self.get_lustre_rpms_installed())
            self._print_info(
                "\nEXAScaler client software packages are removed\n",
                LOG_INFO_LEVEL,
                log_to_console=True,
            )
            return True
        if choise == EXIT:
            self._print_info("Aborting ...", LOG_INFO_LEVEL)
            return False
        if choise == LIST_MOUNT:
            try:
                fsnames = self._query_filesystems_emf_api(self._emf_endpoint)
                mount_cmds = self._query_mount_cmds_emf_api(self._emf_endpoint, fsnames)
                if not mount_cmds:
                    self._print_info(
                        "\nCan't retrieve mount commands from emf api. Aborting...",
                        LOG_WARNING_LEVEL,
                    )
                else:
                    self._print_info("\n", log_to_console=True)
                    for mnt in mount_cmds:
                        self._print_info(
                            "{}  # Filesystem: {}".format(mnt[1], mnt[0]),
                            log_to_console=True,
                        )
            except:
                self._print_info(
                    "An error occured while retrieving info from emf api",
                    LOG_WARNING_LEVEL,
                )

            return True

    def _emf_query(self, target, query):
        rc, out = self._run_cmd(
            [
                "curl",
                "--connect-timeout",
                "3",
                "-v",
                "-k",
                "-H",
                "'content-type:application/json; charset=utf-8'",
                "-d",
                query,
                "https://" + target + ":7443/graphql",
            ]
        )
        return rc, out

    def _get_emf_status(self, target):
        cmd = '\'{"query":"query managerServiceStatus {  managerServiceStatus { serviceStates { service state} running } }"}\''
        return self._emf_query(target, cmd)

    def _find_emf(self, interactive):
        # 1. Use --emf if the user has provided it
        # 2. If --emf hasn't been set, check if emf resolves and ping
        # 3. If that doesn't work and interactive, ask the user for an IP
        # 4. Fail

        # 1
        if self._emf_ip is not None:
            try:
                # emf resolve to something, check if the api is responsive
                rc, out = self._get_emf_status(self._emf_ip)
                if rc == 0:
                    # emf is responsive, use it since user explicitly provided --emf
                    self._print_info(
                        "emf api at  {} seems to work, using it (from --emf)".format(
                            self._emf_ip
                        ),
                        LOG_INFO_LEVEL,
                    )
                    return self._emf_ip
                else:
                    # not responsive or command failed
                    self._print_info(
                        "emf api is not responsive at {} (from --emf)".format(
                            self._emf_ip
                        ),
                        LOG_INFO_LEVEL,
                    )
                    return None
            except:
                self._print_info(
                    "Unknown error while trying to get emf api status from {}".format(
                        self._emf_ip
                    ),
                    LOG_WARNING_LEVEL,
                )
                return None

        else:
            # 2.
            # --emf hasn't been set
            # we try to resolve and ping 'emf'

            rc, out = self._run_cmd(["getent", "hosts", "emf"])
            if rc == 0:
                self._print_info("'emf' resolve, ping the API", LOG_INFO_LEVEL)

                # emf resolve to something, check if the api is responsive
                rc, out = self._get_emf_status("emf")
                if rc == 0:
                    # emf is responsive, ask the user if he wants to use that one since it's implicit
                    self._print_info(
                        "\nemf api is responsive at 'emf'",
                        log_to_console=True,
                    )
                    if yes_no_query(
                        "Do you want to use that one?",
                        "yes",
                        self._yes,
                    ):
                        return "emf"
                else:
                    self._print_info(
                        "emf api at 'emf' is not responsive", LOG_INFO_LEVEL
                    )
            # 3.
            # Everything has failed so far or user didn't want to use 'emf'
            # Ask user for an IP/hostname
            if interactive:
                emf_endpoint_user_input = input(
                    "Please specify emf endpoint (ip or hostname): "
                )
                # check if the api is responsive
                rc, out = self._get_emf_status(emf_endpoint_user_input)
                if rc == 0:
                    return emf_endpoint_user_input
            else:
                # Fail
                self._print_info(
                    "Please add --emf to specify the emf api endpoint",
                    LOG_WARNING_LEVEL,
                )
            return None

    def _query_mount_cmds_emf_api(self, emf, fsnames):
        mnts = []
        mnt_src_template = re.compile(
            r".*\"mountCommand\":\"mount -t lustre.(?P<command>.+)\""
        )
        for fs in fsnames:
            cmd = (
                '\'{"query":"query client {  client {  mountSource(fsName: \\"'
                + fs
                + '\\")  mountCommand(fsName: \\"'
                + fs
                + '\\")  } }"}\''
            )
            rc, out = self._emf_query(str(emf), cmd)
            if rc != 0:
                self._print_info(
                    "\nCan't retrieve mount commands from emf api. Aborting...",
                    LOG_ERROR_LEVEL,
                )
            for line in out.splitlines():
                match = re.match(mnt_src_template, line)
                if match:
                    mnts.append([fs, "mount -t lustre " + match.group("command")])
        return mnts

    def _query_filesystems_emf_api(self, emf):
        rc, out = self._emf_query(
            str(emf),
            '\'{"query" :"query filesystem { filesystem { list {  id stateModifiedAt state name mdtNextIndex ostNextIndex mgsId mdtIds ostIds  }  }}"}\'',
        )
        if rc != 0:
            self._print_info(
                "\nCan't retrieve filesystem list from emf api. Aborting...",
                LOG_ERROR_LEVEL,
            )
        fsname_template = re.compile(r".*\"name\":\"([a-zA-Z0-9]+)\"")
        fsnames = []
        for line in out.splitlines():
            match = re.match(fsname_template, line)
            if match != None:
                fsnames.append(match.group(1))

        return fsnames

    def _perform_validations(self, choise, interactive):
        # Check if install and remove options are not specified together
        if self._install and self._remove:
            self._print_info(
                "Install (-i) & Remove (-r) options cannot be specified together",
                LOG_ERROR_LEVEL,
            )

        # Check if configure and remove options are not specified together
        if self._configure and self._remove:
            self._print_info(
                "Configure (-c) & Remove (-r) options cannot be specified together",
                LOG_ERROR_LEVEL,
            )

        # Validations for install option
        if choise == INSTALL:
            # Check lustre is not already installed
            if self.is_lustre_installed():
                self._print_info(
                    "\nEXAScaler client software packages are already installed. Use --remove to remove first",
                    LOG_WARNING_LEVEL if self._dry_run else LOG_ERROR_LEVEL,
                )

            # Check if MoFED is installed
            if not self._disable_o2ib:
                if self._linux_distribution_name in RHEL_DISTROS:
                    if (
                        self._is_rpm_installed("mlnx-ofa_kernel")
                        and self._is_rpm_installed("kmod-mlnx-ofa_kernel")
                        and self._is_rpm_installed("mlnx-ofa_kernel-devel")
                    ):
                        self._mofed_installed = True
                    else:
                        self._print_info(
                            "\nMellanox OFED is not installed. Lustre will "
                            "be built against in-kernel IB stack.",
                            log_to_console=True,
                        )
                        self._mofed_installed = False

                        if not yes_no_query(
                            "Do you want to continue".format(platform.release()),
                            "yes",
                            self._yes,
                        ):
                            self._print_info(
                                "\nInstall Mellanox OFED with mlnxofedinstall available in "
                                "installer package or install mlnx-ofa_kernel, "
                                "kmod-mlnx-ofa_kernel and mlnx-ofa_kernel-devel packages.",
                                LOG_ERROR_LEVEL,
                            )
                            exit()
                else:
                    if self._is_deb_installed(
                        "mlnx-ofed-kernel-dkms"
                    ) or self._is_deb_installed("mlnx-ofed-kernel-modules"):
                        self._mofed_installed = True
                    else:
                        self._print_info(
                            "\nMellanox OFED is not installed. Lustre will "
                            "be built against in-kernel IB stack.",
                            log_to_console=True,
                        )
                        self._mofed_installed = False

                        if not yes_no_query(
                            "Do you want to continue".format(platform.release()),
                            "yes",
                            self._yes,
                        ):
                            self._print_info(
                                "\nInstall Mellanox OFED with mlnxofedinstall available in "
                                "installer package or install mlnx-ofed-kernel-dkms package.",
                                LOG_ERROR_LEVEL,
                            )
                            exit()
            else:
                self._mofed_installed = False
            # Check if emf install can be ping
            if self._emf_ip is not None:
                rc, out = self._run_cmd(["ping", "-c", "3", self._emf_ip])
                if rc != 0:
                    self._print_info(
                        "\nCan't ping {}. Aborting...".format(self._emf_ip),
                        LOG_ERROR_LEVEL,
                    )
            # Detect if the system is DGX server
            _, processor_info = self._run_cmd(["dmidecode", "-s", "processor-version"])
            if "E5-2698" in processor_info:
                self._dgx_system = "DGX-1"
            elif "8168" in processor_info:
                self._dgx_system = "DGX-2"
            elif "7742" in processor_info:
                self._dgx_system = "DGX-A100"

            self._make_upd_dir()

            if self._dkms and self._emf_ip is None:
                self._print_info(
                    "\nDKMS packages requires --emf option", LOG_ERROR_LEVEL
                )

            if not self._dkms:
                # Check lustre source availability
                # Lustre source defined by --src-dir
                if self._lustre_src:
                    # Not found in specified path, exit and does not attempt to download from EMF
                    if not os.path.exists(self._lustre_src):
                        self._print_info(
                            "\n{0} does not exist".format(self._lustre_src),
                            LOG_ERROR_LEVEL,
                        )
                else:
                    # User hasn't provided --src-dir
                    # We search in the following order:
                    # - local XOR installed archive
                    # - local AND installed archive, ask the user
                    # - ask a path to the user

                    self._lustre_src = ""

                    local_targz = os.path.join(
                        os.path.dirname(self._update_dir), "lustre-source.tar.gz"
                    )
                    local_folder = os.path.join(
                        os.path.dirname(self._update_dir), "lustre-source"
                    )
                    installed_targz = os.path.join(
                        os.path.dirname(self._update_dir),
                        "/usr/share/ddn/lustre-source.tar.gz",
                    )

                    # local XOR installed archive, true if:
                    # - there is a local archive but no installed archive
                    # - there is an installed archive but no local archive
                    # In this case there is no doubt, we take what we find
                    if (
                        os.path.exists(local_folder) or os.path.exists(local_targz)
                    ) ^ os.path.exists(installed_targz):
                        for path in [local_targz, local_folder, installed_targz]:
                            if os.path.exists(path):
                                self._lustre_src = path
                                break

                    # local AND installed archive, ask the user:
                    if not os.path.exists(self._lustre_src):
                        if (
                            os.path.exists(local_folder) or os.path.exists(local_targz)
                        ) and os.path.exists(installed_targz):
                            if yes_no_query(
                                "\nBoth local and installed archives found\nDo you want to install the local one",
                                "yes",
                                self._yes,
                            ):
                                # Take the tar.gz first
                                for path in [local_targz, local_folder]:
                                    if os.path.exists(path):
                                        self._lustre_src = path
                                        break
                            else:
                                self._lustre_src = installed_targz

                    # Last chance before exiting
                    # Ask the user for a path
                    if not os.path.exists(self._lustre_src):
                        if interactive:
                            self._lustre_src = input(
                                "Enter path to lustre source (leave empty to use default source): "
                            )

                    # Exit error, archive not found
                    if not os.path.exists(self._lustre_src):
                        self._print_info(
                            "\nCan't find client archive. Exiting.\n", LOG_ERROR_LEVEL
                        )

                    self._print_info(
                        "\nSelected {} for installation\n".format(self._lustre_src),
                        LOG_INFO_LEVEL,
                        log_to_console=True,
                    )

            else:
                # Check current OS version is available in pre-built DKMS packages
                if self._linux_distribution_name in RHEL_DISTROS:
                    centos_version = "el{}{}".format(
                        self._linux_distribution[1][0], self._linux_distribution[1][2]
                    )
                    if centos_version not in supported_dkms_packages:
                        self._print_info(
                            "Unable to use DKMS packages with current OS version (found {}, must be part of [{}]".format(
                                centos_version, ", ".join(supported_dkms_packages)
                            ),
                            LOG_ERROR_LEVEL,
                        )
                elif self._linux_distribution_name == "ubuntu":
                    ubuntu_version = "".join(
                        ch
                        for ch in "".join(self._linux_distribution[:-1])
                        if ch.isalnum()
                    ).lower()
                    if ubuntu_version not in supported_dkms_packages:
                        self._print_info(
                            "Unable to use DKMS packages with current OS version (found {}, must be part of [{}]".format(
                                ubuntu_version, ", ".join(supported_dkms_packages)
                            ),
                            LOG_ERROR_LEVEL,
                            log_to_console=True,
                        )

        # Validations for configure option
        if choise == CONFIGURE:
            if not self.is_lustre_installed():
                self._print_info(
                    "\nEXAScaler client software packages are not installed. Use --install to install first",
                    LOG_ERROR_LEVEL,
                )
                return True
            if self._is_lustre_mounted():
                self._print_info(
                    "Unmount the lustre filesystem to proceed", LOG_ERROR_LEVEL
                )
            # Retrieve lnet config
            if self._lnets is None:
                default_lnet = self._get_default_lnet()
                if interactive:
                    if default_lnet != None:
                        self._lnets = input(
                            "Specify LNets (semicolon separated) - default ["
                            + default_lnet
                            + "]: "
                        )
                    else:
                        self._lnets = input(
                            "Specify LNets (semicolon separated) - e.g. [o2ib(ens1,ens2)]: "
                        )
                if not self._lnets:
                    if not default_lnet:
                        # User didn't specify lnet and get_default_lnet didn't work
                        self._print_info("Please specify LNets", LOG_ERROR_LEVEL)
                    else:
                        self._lnets = default_lnet
                self._lnets = self._lnets.split(";")

            nic_list = []
            template = re.compile(r"^\s*(?P<lnet>tcp|o2ib)[0-9]*\((?P<nics>.+)\)$")
            for lnet in self._lnets:
                match = re.match(template, lnet)
                if match is None:
                    self._print_info(
                        "Please specify LNets in the correct "
                        "format e.g. o2ib0(ib0,ib1)",
                        LOG_ERROR_LEVEL,
                    )
                nics = match.group("nics").split(",")
                nic_list.extend(nics)

            # Verify if all the nics are available on the system
            for i, nic in enumerate(nic_list):
                # Remove spaces
                nic_list[i] = nic.strip()
                available_nics = os.listdir("/sys/class/net/")
                if nic_list[i].split(":")[0] not in available_nics:
                    self._print_info(
                        "Incorrect interface names specified", LOG_ERROR_LEVEL
                    )

            self._nics = set(nic_list)

            if self._dgx_system:
                default_cpupartitions = DGX_CPU_NPARTITIONS[self._dgx_system]
                if self._cpu_npartitions is None:
                    if interactive:
                        self._cpu_npartitions = input(
                            "Specify cpu_npartitions - ["
                            + default_cpupartitions
                            + "]: "
                        )
                if not self._cpu_npartitions:
                    self._cpu_npartitions = default_cpupartitions

        # Validations for remove option
        if choise == REMOVE:
            if not self.is_lustre_installed():
                self._print_info(
                    "\nEXAScaler client software packages are not installed, nothing to do\n",
                    LOG_INFO_LEVEL,
                    log_to_console=True,
                )
                sys.exit(0)
            if self._is_lustre_mounted():
                self._print_info(
                    "Unmounting the lustre filesystem to proceed",
                    LOG_INFO_LEVEL,
                    log_to_console=True,
                )
                self._is_lustre_mounted(unmount=True)
                self._stop_lustre()

        # Validations for mount option
        if choise == LIST_MOUNT:
            try:
                self._emf_endpoint = self._find_emf(interactive)
            except:
                self._print_info(
                    "\nAn error occured while trying to find emf endpoint",
                    LOG_ERROR_LEVEL,
                )
            if not self._emf_endpoint:
                self._print_info(
                    "\nCan't connect to emf api. Aborting...",
                    LOG_ERROR_LEVEL,
                )

    def upgrade(self):
        """Perform deploy operation."""
        interactive = True
        if self._install or self._configure or self._remove or self._list_mount:
            interactive = False
        exit_loop = False
        self._check_distribution()
        while not exit_loop:
            if interactive:
                choise = self._bootstrap_prompt()
                if choise == EXIT:
                    exit_loop = True
                    continue
                self._perform_validations(choise, interactive)
                self._apply_choise(choise)
            else:
                # _perform_validations and _apply_choise needs to be kept as install and configure can be done at the same time
                if self._install:
                    choise = INSTALL
                    exit_loop = True
                    self._perform_validations(choise, interactive)
                    self._apply_choise(choise)

                if self._configure:
                    choise = CONFIGURE
                    exit_loop = True
                    self._perform_validations(choise, interactive)
                    self._apply_choise(choise)

                if self._remove:
                    choise = REMOVE
                    exit_loop = True
                    self._perform_validations(choise, interactive)
                    self._apply_choise(choise)

                if self._list_mount:
                    choise = LIST_MOUNT
                    exit_loop = True
                    self._perform_validations(choise, interactive)
                    self._apply_choise(choise)

    def clean(self):
        """Cleaning procedure after upgrade."""
        self._print_info("Perform custom cleaning procedure.")
        if self._clean_builddir:
            self._remove_upd_dir()
        self._print_info("Custom cleaning procedure finished.")


def parse_options():
    """Parse command line options."""

    logger.info("Parse script's options")
    p = argparse.ArgumentParser(prog="exa_client_deploy")
    p.add_argument(
        "-i",
        "--install",
        action="store_true",
        help="Install EXAScaler client software",
        default=False,
    )
    p.add_argument(
        "-c",
        "--configure",
        action="store_true",
        help="Configure EXAScaler client software",
        default=False,
    )
    p.add_argument(
        "-m",
        "--list-mount",
        action="store_true",
        help="List EXAScaler mount commands",
        default=False,
    )
    p.add_argument(
        "-r",
        "--remove",
        action="store_true",
        help="Remove EXAScaler client software",
        default=False,
    )
    p.add_argument(
        "-p",
        "--skip-persistent-tuning",
        dest="skip_persistent_tuning",
        action="store_true",
        help="Skip configuring persistency for lustre tuning",
        default=False,
    )
    p.add_argument(
        "-l", "--lnets", dest="lnets", help="Semicolon separated LNets to use"
    )
    p.add_argument(
        "-n",
        "--npartitions",
        dest="cpu_npartitions",
        help="cpu_npartitions for libcfs module (For DGX systems)",
        type=int,
    )
    p.add_argument(
        "-d", "--dry-run", action="store_true", help="Dry run action.", default=False
    )
    p.add_argument(
        "-v", "--verbose", action="count", help="Level of verbosity.", default=0
    )
    p.add_argument(
        "-s",
        "--src-file",
        dest="source",
        help="Path to Lustre source file. If not specified will look in lustre-source.tar.gz and lustre-source",
        default=None,
        type=os.path.abspath,
    )
    p.add_argument(
        "-j",
        "--skip-ro-tuning",
        dest="skip_ro_tuning",
        action="store_true",
        help="Skip Relax Ordering tuning",
        default=False,
    )
    p.add_argument(
        "-k",
        "--skip-eth-tuning",
        dest="skip_eth_tuning",
        action="store_true",
        help="Skip Ethernet tunings",
        default=False,
    )
    p.add_argument(
        "--dkms",
        dest="dkms",
        action="store_true",
        help="Use DKMS installation from EMF repo",
    )
    p.add_argument(
        "--emf",
        dest="emf",
        default=None,
        help="IP/FQDN pointing to your EMF installation",
    )
    p.add_argument(
        "-y",
        "--yes",
        dest="yes",
        action="store_true",
        help="Automatic yes to prompts. Assume 'yes' as answer to all prompts and run non-interactively",
    )
    p.add_argument(
        "--disable-o2ib",
        dest="disable_o2ib",
        action="store_true",
        help="Force disable o2ib related module build",
    )

    return p.parse_args()


def yes_no_query(message, answer="no", force_yes=False):
    possible_answers = {
        "yes": (True, "[Y/n]"),
        "y": (True, "[Y/n]"),
        "no": (False, "[y/N]"),
        "n": (False, "[y/N]"),
    }

    if answer not in possible_answers:
        raise ValueError("Invalid answer: '{0}'".format(answer))

    if force_yes:
        status, prompt = possible_answers["yes"]
        sys.stdout.write("{0} {1}: {2}\n".format(message, prompt, answer))
    else:
        status, prompt = possible_answers[answer]
        while True:
            sys.stdout.write("{0} {1}: ".format(message, prompt))
            flag = input().lower().strip()

            if flag == "":
                break
            elif flag in possible_answers:
                status, prompt = possible_answers[flag]
                break

    return status


def get_distrib_from_os_release_file(full_distribution_name=True):
    # From distro github:
    # The os-release file /etc/os-release if present, with a fall-back on /usr/lib/os-release.
    # The output of the lsb_release command, if available.
    # The distro release file (/etc/*(-|_)(release|version)), if present.
    # The uname command for BSD based distrubtions.
    #     Return information about the current OS distribution as a tuple
    # ``(id_name, version, codename)`` with items as follows:
    # * ``id_name``:  If *full_distribution_name* is false, the result of
    #   :func:`distro.id`. Otherwise, the result of :func:`distro.name`.
    # * ``codename``:  The extra item (usually in parentheses) after the
    #   os-release version number, or the result of :func:`distro.codename`.
    if os.path.exists("/etc/os-release"):
        os_release_file = open("/etc/os-release", "r")
        lines = os_release_file.readlines()
        for line in lines:
            if full_distribution_name:
                raw_name = re.search("^NAME=.*", line)
                if raw_name != None:
                    name, dummy = re.subn(
                        '"', "", re.sub("^NAME=(.*)", r"\1", raw_name.group(0))
                    )
                    continue
            else:
                raw_name = re.search("^ID=.*", line)
                if raw_name != None:
                    name, dummy = re.subn(
                        '"', "", re.sub("^ID=(.*)", r"\1", raw_name.group(0))
                    )
                    continue

            raw_version_id = re.search("^VERSION_ID=.*", line)
            if raw_version_id != None:
                version_id, dummy = re.subn(
                    '"', "", re.sub("^VERSION_ID=(.*)", r"\1", raw_version_id.group(0))
                )
                continue

            # Try to use VERSION_CODENAME if VERSION isn't present
            if not "version_codename" in locals():
                raw_version_codename = re.search("^VERSION_CODENAME=.*", line)
                if raw_version_codename != None:
                    version_codename, dummy = re.subn(
                        '"',
                        "",
                        re.sub(
                            "^VERSION_CODENAME=(.*)",
                            r"\1",
                            raw_version_codename.group(0),
                        ),
                    )
                    continue

            raw_version_codename = re.search("^VERSION=.*", line)
            if raw_version_codename != None:
                version_codename, dummy = re.subn(
                    '"',
                    "",
                    re.sub(".*\((.*)\).*", r"\1", raw_version_codename.group(0)),
                )
                continue

        return (name, version_id, version_codename)
    return None


def run_deploy_procedure():
    """Run ES upgrade procedure."""

    # Parse command line arguments.
    options = parse_options()

    # Initialize updater, perform necessary checks and run upgrade procedure.
    updater = Updater(
        options.source,
        options.lnets,
        options.cpu_npartitions,
        options.emf,
        options.dkms,
        dry_run=options.dry_run,
        verbosity=options.verbose,
        install=options.install,
        remove=options.remove,
        configure=options.configure,
        list_mount=options.list_mount,
        skip_eth_tuning=options.skip_eth_tuning,
        skip_ro_tuning=options.skip_ro_tuning,
        yes=options.yes,
        skip_persistent=options.skip_persistent_tuning,
        disable_o2ib=options.disable_o2ib,
    )
    updater._target_kernel = platform.uname()[2]
    updater.initialize()
    try:
        updater.upgrade()
    finally:
        updater.clean()


if __name__ == "__main__":
    lock_file_path = "/var/run/exa_client_deploy.lock"

    if os.geteuid() != 0:
        exit("\nYou need to have root privileges to run this script. Exiting.\n")

    if sys.version_info[0] != 3:
        exit("\nPlease use python3 to run this script")

    # Check if lock file exists.
    if os.path.exists(lock_file_path):
        with open(lock_file_path, "r") as lock_file:
            pid = int(lock_file.read())
            try:
                # Check is upgrade process active
                os.kill(pid, 0)
            except OSError:
                # Upgrade process is not active. Remove lock file and continue upgrade.
                os.remove(lock_file_path)
            else:
                # Another instance of upgrade script is in progress.
                print("Only one exa client deploy script can run at once.")
                sys.exit(1)

    # Create lock file and write pid of current process to it.
    with open(lock_file_path, "w") as lock_file:
        lock_file.write(str(os.getpid()))
    try:
        # Run update script
        run_deploy_procedure()
    except DeployerException as e:
        print(e)
        exit(1)
    except KeyboardInterrupt:
        print("Procedure was interrupted by user.")
    finally:
        # remove lock file in any case.
        os.remove(lock_file_path)
