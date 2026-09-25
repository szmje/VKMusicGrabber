#!/usr/bin/env python3
# -*- coding: utf-8 -*-
import pytest
from pathlib import Path
from vk_audio_downloader import (
    sanitize_filename,
    ArchiveManager,
    MetadataManager,
    AudioTrack,
    RE_M3U8_TO_MP3,
    parse_playlist_input,
    parse_target_id,
    VKClient,
    demux_ts_to_audio
)
from mutagen.id3 import ID3

def test_sanitize_filename():
    assert sanitize_filename('AC/DC: "Back in Black"?') == "AC_DC_ _Back in Black__"
    assert sanitize_filename('Track\\With/Forbidden:*?"<>|Chars') == "Track_With_Forbidden_______Chars"
    assert sanitize_filename('   Leading and trailing spaces...   ') == "Leading and trailing spaces"
    assert sanitize_filename('') == "audio_track"

def test_audio_track_model():
    track = AudioTrack(
        id=12345,
        owner_id=67890,
        artist="The Prodigy",
        title="Breathe",
        duration=320,
        url="https://example.com/audio.mp3",
        album_title="The Fat of the Land",
        lyrics_id=999
    )
    assert track.uid == "67890_12345"
    assert track.formatted_name == "The Prodigy - Breathe"

def test_archive_manager(tmp_path):
    mgr = ArchiveManager(tmp_path)
    assert mgr.count == 0
    assert not mgr.is_downloaded("100_200")

    mgr.add("100_200")
    assert mgr.is_downloaded("100_200")
    assert mgr.count == 1

    # Reload from disk
    mgr2 = ArchiveManager(tmp_path)
    assert mgr2.is_downloaded("100_200")
    assert not mgr2.is_downloaded("100_201")
    assert mgr2.count == 1

def test_m3u8_conversion_regex():
    sample_m3u8 = "https://psv4.vkuseraudio.net/s/v1/audios/a1b2c3d4/index.m3u8?extra=xyz"
    converted = RE_M3U8_TO_MP3.sub(r'\1/\2.mp3', sample_m3u8)
    assert "/audios/a1b2c3d4.mp3?extra=xyz" in converted

def test_metadata_embedding(tmp_path):
    dummy_mp3 = tmp_path / "test.mp3"
    dummy_mp3.write_bytes(b"\xff\xfb\x90\x00" + b"\x00" * 2000)

    track = AudioTrack(
        id=111,
        owner_id=222,
        artist="Queen",
        title="Bohemian Rhapsody",
        duration=354,
        url="https://example.com/test.mp3",
        album_title="A Night at the Opera"
    )

    lyrics_text = "Is this the real life?\nIs this just fantasy?"
    cover_data = b"\xff\xd8\xff\xe0" + b"\x00" * 100

    MetadataManager.embed_tags(
        file_path=dummy_mp3,
        track=track,
        lyrics=lyrics_text,
        cover_bytes=cover_data
    )

    tags = ID3(str(dummy_mp3))
    assert tags.get("TIT2").text == ["Bohemian Rhapsody"]
    assert tags.get("TPE1").text == ["Queen"]
    assert tags.get("TALB").text == ["A Night at the Opera"]
    uslt = tags.getall("USLT")[0]
    assert "Is this the real life?" in uslt.text
    apic = tags.getall("APIC")[0]
    assert apic.mime == "image/jpeg"
    assert apic.data == cover_data

def test_dual_domain_playlist_parsing():
    res_ru = parse_playlist_input("https://vk.ru/music/playlist/12345_678_key123")
    assert res_ru == (12345, 678, "key123")

    res_com = parse_playlist_input("https://vk.com/music/playlist/-2000123_456")
    assert res_com == (-2000123, 456, None)

    res_album = parse_playlist_input("https://vk.ru/music/album/-9999_555_secret")
    assert res_album == (-9999, 555, "secret")

    res_m = parse_playlist_input("https://m.vk.ru/audio?act=audio_playlist-123_456&access_hash=hash789")
    assert res_m == (-123, 456, "hash789")

    res_raw = parse_playlist_input("12345_678")
    assert res_raw == (12345, 678, None)

def test_dual_domain_target_id_parsing():
    assert parse_target_id(None, "https://vk.ru/id12345") == 12345
    assert parse_target_id(None, "https://vk.com/id12345") == 12345
    assert parse_target_id(None, "https://m.vk.ru/club98765") == -98765
    assert parse_target_id(None, "https://vk.ru/public54321") == -54321
    assert parse_target_id(None, "123456") == 123456
    assert parse_target_id(None, "-123456") == -123456

def test_demux_ts_empty_and_valid():
    assert demux_ts_to_audio(b"") == b""
    # Create fake TS packet: 0x47, PUSI flag, PID=0x100, no adaptation
    header = bytes([0x47, 0x41, 0x00, 0x10])
    # PES header: 00 00 01 C0, pes_len=00 0A, flags=80 00, hdr_data_len=00, audio_bytes=FF FB
    pes = bytes([0x00, 0x00, 0x01, 0xC0, 0x00, 0x0A, 0x80, 0x00, 0x00, 0xFF, 0xFB, 0x90, 0x00])
    packet = header + pes + bytes([0xAA] * (188 - len(header) - len(pes)))
    demuxed = demux_ts_to_audio(packet)
    assert demuxed.startswith(bytes([0xFF, 0xFB, 0x90, 0x00]))
