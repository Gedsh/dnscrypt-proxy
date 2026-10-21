package main

import (
	"bytes"
	"net"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"codeberg.org/miekg/dns"
)

func TestIPRulesAddressMatching(t *testing.T) {
	tests := []struct {
		name    string
		rule    string
		answer  string
		wantIP  string
		matches bool
	}{
		{"mapped exact", "192.0.2.1", "AAAA ::ffff:192.0.2.1", "192.0.2.1", true},
		{"mapped wildcard", "192.0.2.*", "AAAA ::ffff:192.0.2.1", "192.0.2.1", true},
		{"mapped CIDR", "192.0.2.0/24", "AAAA ::ffff:192.0.2.1", "192.0.2.1", true},
		{"IPv4 exact", "192.0.2.1", "A 192.0.2.1", "192.0.2.1", true},
		{"IPv4 wildcard", "192.0.2.*", "A 192.0.2.1", "192.0.2.1", true},
		{"IPv6 exact", "2001:db8::1", "AAAA 2001:db8::1", "2001:db8::1", true},
		{"IPv6 wildcard", "2001:db8:*", "AAAA 2001:db8::1", "2001:db8::1", true},
		{"IPv6 CIDR", "2001:db8::/32", "AAAA 2001:db8::1", "2001:db8::1", true},
		{"mapped nonmatch", "192.0.2.1", "AAAA ::ffff:192.0.2.2", "", false},
		{"mapped wildcard boundary", "192.0.2.*", "AAAA ::ffff:192.0.20.1", "", false},
		{"IPv6 nonmatch", "2001:db8::1", "AAAA 2001:db8::2", "", false},
	}
	for _, tt := range tests {
		for _, allow := range []bool{false, true} {
			kind := "block"
			if allow {
				kind = "allow"
			}
			for _, format := range []string{"tsv", "ltsv"} {
				t.Run(tt.name+"/"+kind+"/"+format, func(t *testing.T) {
					rulesFile := filepath.Join(t.TempDir(), "ips.txt")
					if err := os.WriteFile(rulesFile, []byte(tt.rule+"\n"), 0o600); err != nil {
						t.Fatal(err)
					}
					proxy := &Proxy{allowedIPFile: rulesFile, blockIPFile: rulesFile}
					var log bytes.Buffer
					var plugin Plugin
					if allow {
						p := new(PluginAllowedIP)
						if err := p.Init(proxy); err != nil {
							t.Fatal(err)
						}
						p.logger, p.format = &log, format
						plugin = p
					} else {
						p := new(PluginBlockIP)
						if err := p.Init(proxy); err != nil {
							t.Fatal(err)
						}
						p.logger, p.format = &log, format
						plugin = p
					}
					answer, err := dns.New("example.org. 60 IN " + tt.answer)
					if err != nil {
						t.Fatal(err)
					}
					msg := dns.NewMsg("example.org.", dns.RRToType(answer))
					msg.Response = true
					msg.Answer = []dns.RR{answer}
					if err := msg.Pack(); err != nil {
						t.Fatal(err)
					}
					msg = &dns.Msg{Data: msg.Data}
					if err := msg.Unpack(); err != nil {
						t.Fatal(err)
					}
					client := net.Addr(&net.UDPAddr{IP: net.ParseIP("127.0.0.1"), Port: 53000})
					state := NewPluginsState(proxy, "udp", &client, "udp", time.Now())
					state.qName = "example.org"
					if err := plugin.Eval(&state, msg); err != nil {
						t.Fatal(err)
					}
					matched := state.action == PluginsActionReject
					if allow {
						matched = state.sessionData["whitelisted"] == true
					}
					if matched != tt.matches {
						t.Errorf("rule %q matched %q: %v, want %v", tt.rule, tt.answer, matched, tt.matches)
					}
					if tt.matches {
						field := "\t" + tt.wantIP + "\n"
						if format == "ltsv" {
							field = "\tip:" + tt.wantIP + "\n"
						}
						if !strings.HasSuffix(log.String(), field) {
							t.Errorf("log %q does not end with %q", log.String(), field)
						}
					} else if log.Len() != 0 {
						t.Errorf("nonmatching rule produced log %q", log.String())
					}
				})
			}
		}
	}
}
