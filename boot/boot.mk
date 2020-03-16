
ipxe-chainloader:
	@echo '#!ipxe' > boot/chainload.ipxe
	@echo 'dhcp' >> boot/chainload.ipxe
	@echo "echo Chainloading from $(IPXE_CHAINLOADER_HOST)" >> boot/chainload.ipxe
	@echo "chain http://$(IPXE_CHAINLOADER_HOST):8081/boot.ipxe" >> boot/chainload.ipxe
	$(MAKE) -C boot/ipxe/src EMBED=../../chainload.ipxe

PHONY += ipxe-chainloader
