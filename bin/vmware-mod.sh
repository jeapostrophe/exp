#!/bin/sh

ln -s /usr/src/linux-$(uname -r)/include/generated/uapi/linux/version.h /usr/src/linux-$(uname -r)/include/linux/
vmware-modconfig --console --install-all
