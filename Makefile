IMAGE ?= shopping-sessions:latest
CPUS  ?= 8
MEM   ?= 24g
PLATFORM ?= linux/amd64
DEV   ?= dev
ANSWER ?= dev-answer
export IMAGE CPUS MEM PLATFORM

.PHONY: build fixtures dev run-dev check-dev local-fixtures

build:
	docker buildx build --platform $(PLATFORM) --load -t $(IMAGE) .

fixtures: build
	python3 scripts/run_fixtures.py fixtures -- scripts/docker_run.sh

dev:
	generate --seed 1 --events 1000000 --clicks 250000 --output $(DEV)

run-dev: build
	rm -rf out && time scripts/docker_run.sh $(DEV) out

check-dev:
	python3 scripts/compare.py out $(ANSWER)

# Without Docker: cargo build --release, then run the fixtures on the binary.
local-fixtures:
	cargo build --release
	python3 scripts/run_fixtures.py fixtures -- target/release/sess
